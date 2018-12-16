import z3


def conj(a, b):
    return z3.And(a, b)


def disj(a, b):
    return z3.Or(a, b)


class VariableSemantic:
    def __init__(self, name):
        self.len = z3.Int(name + '.len')
        self.max = z3.Int(name + '.max')
        self.min = z3.Int(name + '.min')
        self.first = z3.Int(name + '.first')
        self.last = z3.Int(name + '.last')


class FunctionSemantic:
    def __init__(self, addr, input_length, lambdas):
        self.addr = ','.join(map(str, ['root'] + addr))
        self.inputs = list()
        for i in range(input_length):
            self.inputs.append(VariableSemantic('v_in_%s_%d' % (self.addr, i)))
        self.output = VariableSemantic('v_out_%s' % self.addr)
        self.spec = list()
        self.set_spec(lambdas)

    def set_spec(self, lambdas):
        for l in lambdas:
            self.spec.append(l(self.inputs, self.output))

    def find_index(self, spec):
        return self.spec.index(spec)


class SmtSolver:
    def __init__(self):
        self.output = None
        self.inputs = list()
        self.spec_map = None
        self.solver = z3.Solver()
        pass

    @classmethod
    def unsat(cls, formula):
        solver = z3.Solver()
        solver.add(formula)
        return solver.check() == z3.unsat

    @classmethod
    def get_spec(cls, x, v):
        spec = []
        if type(x) == int:
            spec += [v.len == 1,
                     v.max == x,
                     v.min == x,
                     v.first == x,
                     v.last == x]
        elif type(x) == list:
            if len(x) > 0:
                spec += [v.len == len(x),
                         v.max == max(x),
                         v.min == min(x),
                         v.first == x[0],
                         v.last == x[-1]]
            else:
                spec = [v.len == len(x)]
        return spec

    def build_spec(self, examples, inputs, output):
        spec = []
        self.output = output
        self.inputs = inputs[:len(examples[0][0])]
        for i, (inputs, output) in enumerate(examples):
            output_spec = SmtSolver.get_spec(output, self.output)
            input_specs = []
            for j, input_example in enumerate(inputs):
                input_spec = SmtSolver.get_spec(input_example, self.inputs[j])
                input_specs += input_spec
            example_spec = output_spec + input_specs
            spec.append(example_spec)
        return spec

    def get_abstract_spec(self, examples):
        SPECS_X_Y = [
            lambda x, y: conj(x.len >= 1, y.len == 1),
            lambda x, y: x.len == y.len,
            lambda x, y: x.len > y.len,
            lambda x, y: x.len >= y.len,
            lambda x, y: x.max >= y.max,
            lambda x, y: x.max == y.max,
            lambda x, y: x.min <= y.min,
            lambda x, y: x.min == y.min,
            lambda x, y: x.first == y.first,
            lambda x, y: x.first == y.last,
            lambda x, y: x.last == y.first,
            lambda x, y: x.last == y.last,

            lambda x, y: x.min == y.first,
            lambda x, y: x.max == y.last,
            lambda x, y: x.max == y.len,
            lambda x, y: x.len >= y.first,
        ]
        SPECS_XS = [
            lambda xs: conj(xs[0].first > 0, xs[0].first < xs[1].len),
            lambda xs: conj(xs[0].first >= 0, xs[0].first <= xs[1].len),
            lambda xs: conj(xs[1].first >= 0, xs[1].first <= xs[0].len),
            lambda xs: conj(xs[1].first >= 0, xs[1].first <= xs[0].len),
        ]
        SPECS_Y = [
            lambda y: y.first >= 0,
            lambda y: y.first > 0,
        ]
        SPECS_XS_Y = [
            lambda xs, y: disj(conj(xs[0].len <= xs[1].len, xs[0].len == y.len),
                               conj(xs[1].len <= xs[0].len, xs[1].len == y.len))
        ]
        solver = z3.Solver()
        abstract_specs = list()
        generics = list()
        for x in self.inputs:
            for spec_gen in SPECS_X_Y:
                spec = spec_gen(x, self.output)
                include = True
                for example in examples:
                    solver.push()
                    solver.add(spec)
                    include = solver.check(*example) != z3.unsat and include
                    solver.pop()
                if include:
                    abstract_specs.append(spec)
                    generics.append(spec_gen)
        if len(self.inputs) > 1:
            for spec_gen in SPECS_XS:
                spec = spec_gen(self.inputs)
                include = True
                for example in examples:
                    solver.push()
                    solver.add(spec)
                    include = solver.check(example) != z3.unsat and include
                    solver.pop()
                if include:
                    abstract_specs.append(spec)
                    generics.append(spec_gen)
            for spec_gen in SPECS_XS_Y:
                spec = spec_gen(self.inputs, self.output)
                include = True
                for example in examples:
                    solver.push()
                    solver.add(spec)
                    include = solver.check(example) != z3.unsat and include
                    solver.pop()
                if include:
                    abstract_specs.append(spec)
                    generics.append(spec_gen)
        for spec_gen in SPECS_Y:
            spec = spec_gen(self.output)
            include = True
            for example in examples:
                solver.push()
                solver.add(spec)
                include = solver.check(example) != z3.unsat and include
                solver.pop()
            if include:
                abstract_specs.append(spec)
                generics.append(spec_gen)
        return abstract_specs, generics

    def build_program_spec(self, program):
        return program.infer_spec(self.output, self.inputs)

    def set_example_spec(self, specs, abs_specs=list()):
        io_spec = list()
        for i, example_spec in enumerate(specs):
            ex_spec = list()
            for j, constraint in enumerate(example_spec):
                ex_spec.append(constraint)
            io_spec.append(z3.And(*ex_spec))
        io_constraint = z3.Or(*io_spec)
        self.solver.assert_and_track(io_constraint, 'e')
        for i, constraint in enumerate(abs_specs):
            self.solver.assert_and_track(constraint, 'a%d' % i)

    def solve(self, wire_specs, program_specs, spec_map):
        unsat_cores = list()
        self.solver.push()
        p_specs = list()
        for i, constraint in enumerate(wire_specs):
            self.solver.assert_and_track(constraint, 'w%d' % i)
        for i, constraint in enumerate(program_specs):
            marker = z3.Bool('p%d' % i)
            p_specs.append(marker)
            self.solver.assert_and_track(constraint, marker)
        # self.solver.add(ss)
        if self.solver.check() == z3.unsat:
            for unsat_spec_symbol in self.solver.unsat_core():
                if unsat_spec_symbol in p_specs:
                    spec = program_specs[p_specs.index(unsat_spec_symbol)]
                    node, component = spec_map[spec]
                    unsat_cores.append((spec, node, component))
        self.solver.pop()
        return unsat_cores
