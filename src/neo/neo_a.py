from neo.partial import ProgramNode
from neo.dsl import Dsl, Variable
from sat.solver import SatSolver
from smt.solver import SmtSolver
from deepcoder.dsl.function import OutputOutOfRangeError, NullInputError
import timeout_decorator

ERASE_LINE = '\x1b[2K'


class NeoA(object):
    def __init__(self, dsl, max_depth):
        self.dsl = dsl
        self.max_depth = max_depth

        self.specs = list()
        self.abs_specs = list()
        self.lemmas = SatSolver.initialize_formula()
        self.model = None
        self.output_type = None
        self.examples = None
        self.programs_seen = set()
        self.sat = SatSolver(self.dsl)
        self.smt = SmtSolver()

    def set_specs(self, examples):
        self.specs = self.smt.build_spec(examples, self.dsl.generic_x, self.dsl.generic_y)
        self.abs_specs, generics = self.smt.get_abstract_spec(self.specs)
        self.specs = self.specs[:3]
        self.output_type = Dsl.get_type(self.examples[0][1])
        self.smt.set_example_spec(self.specs, self.abs_specs)

    @timeout_decorator.timeout(3 * 60)
    def synthesize(self, examples, prediction):
        self.examples = examples
        self.model = prediction
        self.set_specs(examples)

        program = ProgramNode()
        program.set_type(self.output_type)
        result = self.synthesize_step(program)
        if result is not None:
            program, _ = result
            return True, program
        else:
            return False, None

    def synthesize_step(self, program, check=False):
        if program.is_concrete():
            return program, False

        candidates = self.decide(program)
        current = self.sat.encode_program(program)
        for hole, component, _ in candidates:
            self.sat.program_sat_encoding = current
            program_new = self.propagate(program, hole, component)
            name = str(program_new)
            if name in self.programs_seen:
                continue
            print(ERASE_LINE + name, end='\r')
            self.programs_seen.add(name)
            if component not in self.dsl.lambdas and (check or type(component) is Variable):
                conflicts = self.check_conflict(program_new)
                if len(conflicts) > 0:
                    new_lemmas = self.sat.unit_propagate(
                        self.lemmas & self.analyze_conflict(conflicts))
                    if new_lemmas is None:
                        return None
                    else:
                        self.lemmas = new_lemmas
                    self.backtrack(program_new)
            result = self.synthesize_step(program_new, check=program_new.has_variable())
            if result is not None:
                program_concrete, checked = result
                if checked:
                    return result
                elif self.validate_concrete(program_concrete):
                    return program_concrete, True
                    # else:
                    #     self.lemmas = self.lemmas & (
                    #             -current_encoding | -self.sat.create_variable(hole, component))
        return None

    def decide(self, program):
        # V <- {(H, p) | H \in Holes(P), p = A_H -> X(A_1...A_k)}
        # V' <- {(H, p) \in V | Fill(P, H, p) ~ lemmas}
        holes, num_components = program.get_holes()
        fills = list()
        for hole in holes:
            candidates = self.dsl.get_components_of_type(hole.output_type, variable_only=(
                    len(hole.addr) >= self.max_depth or num_components >= self.max_depth))
            for component in candidates:
                if component in self.dsl.terms:
                    score = self.model[self.dsl.terms.index(component)]
                else:
                    score = 1
                encoding = self.sat.program_sat_encoding & self.sat.encode_node(hole, component)
                if self.sat.unit_propagate(encoding & self.lemmas):
                    fills.append((hole, component, score))
        # argmax(H, p) \in V' L_\theta(Fill(H, H, p) | self.specs)
        return self.rank(fills)

    def rank(self, fills):
        lambdas = list()
        others = list()
        for hole, component, score in fills:
            if component in self.dsl.lambdas:
                lambdas.append((hole, component, score))
            else:
                others.append((hole, component, score))
        lambdas.sort(key=lambda x: -x[2])
        others.sort(key=lambda x: -x[2])
        return others + lambdas

    def propagate(self, program, node, component):
        # P <- Fill(P, H, p)
        program_new = program.copy(self.dsl)
        node = program_new.get_node(node.addr)
        node.set_component(component, self.dsl, True)
        self.sat.assign(node, component, len(node.addr))
        return program_new

    def check_conflict(self, program):
        wire_spec, program_spec, spec_map = self.smt.build_program_spec(program)
        muc = self.smt.solve(wire_spec, program_spec, spec_map)
        return muc

    def analyze_conflict(self, conflicts):
        lemmas = self.sat.initialize_formula()
        for spec, node, component in conflicts:
            if component in self.dsl.functions:
                prop_idx = node.semantics.find_index(spec)
                generic_prop = self.dsl.generic_specs[str(component)][prop_idx]
                modulo_fn_names = self.dsl.prop_to_fn[str(generic_prop) + '|' + str(component.type)]
                components = [c for c in self.dsl.functions if
                              c.name in modulo_fn_names and c.type == component.type]
            else:
                components = [component]
            # find components with matching types of the component & semantic component
            # block those components from being assigned
            lemmas |= self.sat.encode_lemma(node, components)
        return lemmas

    def backtrack(self, program):
        # get variables in lemma with decision levels
        level_map = self.sat.get_lemma_vars_by_decision_levels()
        pairs = self.sat.get_var_node_pairs(program.get_node_list())
        candidates = dict()
        for level in level_map:
            vars = level_map[level]
            for var, node in pairs:
                if var.name in vars:
                    if level in candidates:
                        candidates[level].append(node)
                    else:
                        candidates[level] = [node]
        candidate_list_of_list = [candidates[level] for level in candidates]
        if len(candidate_list_of_list) == 1:
            for node_to_remove in candidate_list_of_list[0]:
                node_to_remove.clear()
        elif len(candidate_list_of_list) > 1:
            for node_to_remove in candidate_list_of_list[1]:
                node_to_remove.clear()
        self.sat.update_encoding(program)  # TODO: is this necessary?

    def validate_concrete(self, program):
        for inputs, output in self.examples:
            if not self.validate_concrete_example(program, inputs, output):
                return False
        return True

    def validate_concrete_example(self, program, inputs, output):
        try:
            return program.run(inputs).val == output
        except (OutputOutOfRangeError, NullInputError):
            return False
