import satispy
from deepcoder.dsl.impl import LAMBDAS


class SatSolver:
    def __init__(self, dsl):
        self.solver = satispy.solver.Minisat('minisat %s %s -no-luby -rinc=1.5 -phase-saving=0 -rnd-freq=0.02 > /dev/null')
        self.components = dsl.components
        self.program_sat_encoding = SatSolver.initialize_formula()
        self.var_map = dict()
        self.decision_map = dict()
        self.lemma_vars = set()

    @classmethod
    def initialize_formula(self):
        return satispy.Cnf()

    def create_variable(self, node, component):
        prefix = ','.join(map(str, node.addr))
        var_name = "root,%s|%s" % (prefix, component)
        if var_name in self.var_map:
            var = self.var_map[var_name]
        else:
            var = satispy.Variable(var_name)
            self.var_map[var_name] = var
        return var

    def encode_program(self, program):
        node_list = program.get_node_list()
        encoded = satispy.Cnf()
        for node, assigned in node_list:
            if assigned is not None:
                encoded &= self.encode_node(node, assigned)
        return encoded

    def encode_node(self, node, assigned):
        encoded = self.create_variable(node, assigned)
        return encoded

    def encode_lemma(self, node, components):
        encoded = satispy.Cnf()
        for component in components:
            var = self.create_variable(node, component)
            self.lemma_vars.add(var.name)
            encoded &= -var
        return encoded

    def solve(self, exp):
        solution = self.solver.solve(exp)
        return solution.success

    def valid(self, exp):
        return not self.solve(-exp)

    def encode_r(self, r, node):
        encoded_r = satispy.Cnf()
        for alt in r:
            encoded_r |= self.encode_node(node, alt)
        return encoded_r

    def implies_assignment(self, node, component, encoded_r, lemmas):
        rhs = self.create_variable(node, component)
        lhs = lemmas & encoded_r & self.program_sat_encoding
        propagated = self.unit_propagate(lhs)
        if propagated is None:
            return False
        else:
            for clause in propagated.dis:
                if len(clause) == 1 and rhs in clause:
                    print.debug('rhs', rhs)
                    print.debug('lemmas', lemmas)
                    print.debug('encoded_r', encoded_r)
                    print.debug('program', self.program_sat_encoding)
                    logger.debug('implication', lhs & rhs)
                    logger.debug('validity', -(lhs & rhs))
                    logger.debug('propagated', propagated)
                    exit(1)
                    return True
            return False

    def assign(self, node, component, decision_level):
        self.program_sat_encoding &= self.encode_node(node, component)
        addr = "root,%s|" % ','.join(map(str, node.addr))
        for level in self.decision_map:
            self.decision_map[level] = [x for x in self.decision_map[level] if not x.startswith(addr)]
        if decision_level in self.decision_map:
            self.decision_map[decision_level].append("%s%s" % (addr, component))
        else:
            self.decision_map[decision_level] = ["%s%s" % (addr, component)]
        return self.program_sat_encoding

    def get_lemma_vars_by_decision_levels(self):
        level_map = dict()
        for level in self.decision_map:
            lemma_vars = list()
            for var_name in self.decision_map[level]:
                if var_name in self.lemma_vars:
                    lemma_vars.append(var_name)
            if len(lemma_vars) > 0:
                level_map[level] = lemma_vars
        return level_map

    def get_var_node_pairs(self, pair_list):
        pairs = list()
        for node, component in pair_list:
            var = self.create_variable(node, component)
            pairs.append((var, node))
        return pairs

    def update_encoding(self, program):
        self.program_sat_encoding = self.encode_program(program)

    def unit_propagate(self, encoding):
        if len(encoding.dis) == 1:
            return encoding
        unit_clause_vars = set()
        for clause in encoding.dis:
            if len(clause) == 1:
                for variable in clause:
                    unit_clause_vars.add(variable)
            elif len(clause) == 0:
                return None
        if len(unit_clause_vars) == 0:
            return encoding
        changed = False
        current_dis = encoding.dis
        for var in unit_clause_vars:
            dis = list()
            for clause in current_dis:
                negvar = -var
                if negvar in clause:
                    changed = True
                    dis.append(frozenset([x for x in clause if negvar != x]))
                else:
                    dis.append(clause)
            current_dis = dis
        if changed:
            new_encoding = satispy.Cnf()
            new_encoding.dis = current_dis
            return self.unit_propagate(new_encoding)
        else:
            return encoding
