from neo.dsl import Dsl
from neo.partial import ProgramNode
from deepcoder.dsl.function import OutputOutOfRangeError, NullInputError
import timeout_decorator

ERASE_LINE = '\x1b[2K'


class Base(object):
    def __init__(self, dsl, max_depth):
        self.dsl = dsl
        self.examples = None
        self.model = None
        self.output_type = None
        self.programs_seen = set()
        self.max_depth = max_depth

    @timeout_decorator.timeout(3 * 60)
    def synthesize(self, examples, prediction):
        self.model = prediction
        self.examples = examples
        self.output_type = Dsl.get_type(self.examples[0][1])

        program = ProgramNode()
        program.set_type(self.output_type)
        result = self.synthesize_step(program)
        if result is not None:
            program, _ = result
            return True, program
        else:
            return False, None

    def synthesize_step(self, program):
        if program.is_concrete():
            return program, False

        candidates = self.decide(program)
        for hole, component, _ in candidates:
            program_new = self.propagate(program, hole, component)
            name = str(program_new)
            if name in self.programs_seen:
                continue
            print(ERASE_LINE + name, end='\r')
            self.programs_seen.add(name)
            result = self.synthesize_step(program_new)
            if result is not None:
                program_concrete, checked = result
                if checked:
                    return result
                elif self.validate_concrete(program_concrete):
                    return program_concrete, True
        return None

    def decide(self, program):
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
                fills.append((hole, component, score))
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
        program_new = program.copy(self.dsl)
        node = program_new.get_node(node.addr)
        node.set_component(component, self.dsl, False)
        return program_new

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
