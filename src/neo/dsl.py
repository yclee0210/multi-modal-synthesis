import z3

'''
x0.len >= 1
y.len >= 0
x0.len >= y.len
x0.max >= y.max
x0.min <= y.min
x0.first == y.first
'''

from deepcoder.dsl.impl import FUNCTIONS, LAMBDAS
from deepcoder.dsl.types import INT, LIST, BOOL, FunctionType
from deepcoder.dsl.value import Value

from smt.solver import conj, disj, VariableSemantic, FunctionSemantic

HEAD = ('HEAD', 1, [
    lambda xs, y: conj(xs[0].len >= 1, y.len == 1),
    lambda xs, y: xs[0].max >= y.max,
    lambda xs, y: xs[0].min <= y.min,
    lambda xs, y: y.first == xs[0].first,
    lambda xs, y: y.last == y.first,
    lambda xs, y: y.min == y.last,
    lambda xs, y: y.max == y.min,
    lambda xs, y: y.len == 1
])
TAIL = ('TAIL', 1, [
    lambda xs, y: conj(xs[0].len >= 1, y.len == 1),
    lambda xs, y: xs[0].max >= y.max,
    lambda xs, y: xs[0].min <= y.min,
    lambda xs, y: y.first == xs[0].last,
    lambda xs, y: y.last == xs[0].last,
    lambda xs, y: y.last == y.first,
    lambda xs, y: y.min == y.last,
    lambda xs, y: y.max == y.min,
    lambda xs, y: y.len == 1
])
MINIMUM = ('MINIMUM', 1, [
    lambda xs, y: conj(xs[0].len >= 1, y.len == 1),
    lambda xs, y: xs[0].max >= y.max,
    lambda xs, y: xs[0].min == y.min,
    lambda xs, y: y.last == y.first,
    lambda xs, y: y.min == y.last,
    lambda xs, y: y.max == y.min,
    lambda xs, y: y.len == 1
])
MAXIMUM = ('MAXIMUM', 1, [
    lambda xs, y: conj(xs[0].len >= 1, y.len == 1),
    lambda xs, y: xs[0].max == y.max,
    lambda xs, y: xs[0].min <= y.min,
    lambda xs, y: y.last == y.first,
    lambda xs, y: y.min == y.last,
    lambda xs, y: y.max == y.min,
    lambda xs, y: y.len == 1
])
REVERSE = ('REVERSE', 1, [
    lambda xs, y: xs[0].len == y.len,
    lambda xs, y: xs[0].max == y.max,
    lambda xs, y: xs[0].min == y.min,
    lambda xs, y: y.first == xs[0].last,
    lambda xs, y: y.last == xs[0].first,
    lambda xs, y: y.last == y.first,
    lambda xs, y: y.min == y.last,
    lambda xs, y: y.max == y.min,
    lambda xs, y: y.len == 1
])
SORT = ('SORT', 1, [
    lambda xs, y: xs[0].len == y.len,
    lambda xs, y: xs[0].max == y.max,
    lambda xs, y: xs[0].min == y.min,
    lambda xs, y: y.first == xs[0].min,
    lambda xs, y: y.last == xs[0].max
])
SUM = ('SUM', 1, [
    lambda xs, y: conj(xs[0].len >= 1, y.len == 1),
    lambda xs, y: y.last == y.first,
    lambda xs, y: y.min == y.last,
    lambda xs, y: y.max == y.min,
    lambda xs, y: y.len == 1
])
TAKE = ('TAKE', 2, [
    lambda xs, y: xs[0].max == y.len,
    lambda xs, y: xs[1].len >= y.len,
    lambda xs, y: xs[1].max >= y.max,
    lambda xs, y: xs[1].min <= y.min,
    lambda xs, y: conj(xs[0].first >= 0, xs[0].first <= xs[1].len),
    lambda xs, y: xs[1].first == y.first
])
DROP = ('DROP', 2, [
    lambda xs, y: xs[1].len > y.len,
    lambda xs, y: xs[1].max >= y.max,
    lambda xs, y: xs[1].min <= y.min,
    lambda xs, y: conj(xs[0].first > 0, xs[0].first < xs[1].len),
    lambda xs, y: xs[1].last == y.last
])
ACCESS = ('ACCESS', 2, [
    lambda xs, y: conj(xs[1].len >= 1, y.len == 1),
    lambda xs, y: xs[1].max >= y.max,
    lambda xs, y: xs[1].min <= y.min,
    lambda xs, y: conj(xs[0].first > 0, xs[0].first < xs[1].len),
    lambda xs, y: y.last == y.first,
    lambda xs, y: y.min == y.last,
    lambda xs, y: y.max == y.min,
    lambda xs, y: y.len == 1
])
MAP = ('MAP', 2, [
    lambda xs, y: xs[1].len == y.len
])
FILTER = ('FILTER', 2, [
    lambda xs, y: xs[1].len > y.len,
    lambda xs, y: xs[1].max >= y.max,
    lambda xs, y: xs[1].min <= y.min,
])
COUNT = ('COUNT', 2, [
    lambda xs, y: conj(xs[1].len >= 1, y.len == 1),
    lambda xs, y: y.first >= 0,
    lambda xs, y: xs[1].len >= y.first,
    lambda xs, y: y.last == y.first,
    lambda xs, y: y.min == y.last,
    lambda xs, y: y.max == y.min,
    lambda xs, y: y.len == 1
])
SCAN1L = ('SCAN1L', 2, [
    lambda xs, y: y.len == xs[1].len,
    lambda xs, y: y.first == xs[1].first
])
ZIPWITH = ('ZIPWITH', 3, [
    lambda xs, y: disj(conj(xs[1].len <= xs[2].len, xs[1].len == y.len), conj(xs[2].len <= xs[1].len, xs[2].len == y.len))
])

SEMANTICS = [
    HEAD,
    TAIL,
    MINIMUM,
    MAXIMUM,
    REVERSE,
    SORT,
    SUM,

    TAKE,
    DROP,
    ACCESS,

    MAP,
    FILTER,
    COUNT,
    SCAN1L,
    ZIPWITH
]


class Variable(Value):
    def __init__(self, index, value):
        if type(value) == int:
            super(Variable, self).__init__(value, INT)
        elif type(value) == list:
            super(Variable, self).__init__(value, LIST)
        else:
            raise ValueError('bad type')
        self.index = index
        self._name = 'x%d' % index

    @property
    def output_type(self):
        return self.type


class Dsl:
    def __init__(self):
        self.variables = []
        self.components = []
        self.functions = [f for f in FUNCTIONS if f not in LAMBDAS]
        self.lambdas = LAMBDAS
        self.terms = self.functions + self.lambdas
        self.generic_x = [VariableSemantic('x%d' % i) for i in range(3)]
        self.generic_y = VariableSemantic('y')
        self.semantics = dict(
            [(name, (input_length, lambdas)) for
             name, input_length, lambdas in SEMANTICS])
        self.generic_specs = dict([(name, self.get_generic_specs(lambdas, self.generic_x, self.generic_y)) for
                                   name, input_length, lambdas in SEMANTICS])
        self.props, self.prop_to_fn = self.set_props()

    def set_props(self):
        props = list()
        prop_to_fn = dict()
        solver = z3.Solver()
        for fn_name, ls in self.generic_specs.items():
            fn = None
            for func in self.functions:
                if func.name == fn_name:
                    fn = func
                    break
            for l in ls:
                for fn_2_name, ls_2 in self.generic_specs.items():
                    fn_2 = None
                    for func in self.functions:
                        if func.name == fn_2_name:
                            fn_2 = func
                            break
                    if fn.type == fn_2.type:
                        solver.add(z3.Implies(z3.And(*ls_2), l))
                        if solver.check() != z3.unsat:
                            prop = str(l) + '|' + str(fn.type)
                            if prop in prop_to_fn:
                                prop_to_fn[prop].add(fn_2_name)
                            else:
                                props.append(prop)
                                prop_to_fn[prop] = set()
                                prop_to_fn[prop].add(fn_2_name)
                        solver.reset()
        return props, prop_to_fn

    def get_likely(self, specs):
        unique = list()
        for fn_name, ls in self.generic_specs.items():
            props = set([l for l in ls])
            for fn_name_2, ls_2 in self.generic_specs.items():
                if fn_name != fn_name_2:
                    props2 = set([l for l in ls_2])
                    props = props - props2
            if len(props) > 0:
                unique.append((fn_name, list(props)))
        solver = z3.Solver()
        likely = None
        for spec in specs:
            like = set()
            for fn_name, ls in self.generic_specs.items():
                solver.push()
                solver.add(z3.Implies(spec, z3.Not(z3.Or(*ls))))
                if solver.check(spec) != z3.unsat:
                    like.add(fn_name)
                solver.pop()
            if likely is None:
                likely = like
            else:
                likely &= like
        print(likely)
        return likely


    def set_variables(self, problem):
        inputs = problem['examples'][0]['inputs']
        self.variables = [Variable(i, x) for i, x in enumerate(inputs)]
        self.components = self.variables + self.terms

    @classmethod
    def get_type(cls, const):
        if type(const) == int:
            return INT
        elif type(const) == list:
            return LIST
        else:
            return None

    def get_generic_specs(self, lambdas, xs, y):
        specs = list()
        for l in lambdas:
            specs.append(l(xs, y))
        return specs

    def get_components_of_type(self, output_type, variable_only=False):
        if type(output_type) == FunctionType:
            return [l for l in self.lambdas if l.type == output_type]
        elif variable_only:
            return [x for x in self.variables if x.output_type == output_type]
        else:
            variables = [x for x in self.variables if x.output_type == output_type]
            functions = [f for f in self.functions if f.output_type == output_type]
            return variables + functions
