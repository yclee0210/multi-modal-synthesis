from neo.dsl import Variable, FunctionSemantic
from deepcoder.dsl.impl import LAMBDAS
from deepcoder.dsl.value import Value
from deepcoder.dsl.types import INT, LIST


class ProgramNode:
    def __init__(self, addr=list()):
        self.output_type = None
        self.component = None
        self.children = []
        self.semantics = None
        self.addr = addr
        self.spec_map = dict()

    def set_type(self, output_type):
        self.output_type = output_type

    def set_component(self, component, dsl, neo=True):
        self.component = component
        self.spec_map = dict()
        if component is not None and not type(component) == Variable and component not in LAMBDAS:
            input_length, spec_generators = dsl.semantics[component.name]
            if neo:
                self.semantics = FunctionSemantic(self.addr, input_length, spec_generators)
                spec = self.semantics.spec
                for s in spec:
                    self.spec_map[s] = (self, self.component)
            for i in range(len(self.component.type.input_types)):
                child = ProgramNode(self.addr + [i])
                child.set_type(self.component.type.input_types[i])
                self.children.append(child)

    def get_components(self):
        if self.component is None:
            return set()
        else:
            components = set()
            components.add(self.component)
            for child in self.children:
                components |= child.get_components()
            return components

    def is_concrete(self):
        if self.component is None:
            return False
        else:
            result = True
            for child in self.children:
                result = result and child.is_concrete()
            return result

    def get_node_list(self):
        nodes = list()
        if self.component is None:
            nodes.append((self, None))
        else:
            nodes.append((self, self.component))
            for i, child in enumerate(self.children):
                nodes += child.get_node_list()
        return nodes

    def get_holes(self):
        holes = list()
        if self.component is None:
            return [self], 0
        else:
            count = 1
            for child in self.children:
                child_holes, child_count = child.get_holes()
                holes += child_holes
                count += child_count
            return holes, count

    def has_variable(self):
        if self.component is None:
            return False
        elif type(self.component) is Variable:
            return True
        else:
            for child in self.children:
                if child.has_variable():
                    return True
            return False

    def copy(self, dsl):
        node_new = ProgramNode()
        node_new.set_type(self.output_type)
        node_new.addr = self.addr
        if self.component is not None:
            node_new.component = self.component
            node_new.semantics = self.semantics
            if node_new.semantics is not None:
                node_new.spec_map = dict()
                spec = node_new.semantics.spec
                for s in spec:
                    node_new.spec_map[s] = (node_new, node_new.component)
            for child in self.children:
                child_new = child.copy(dsl)
                node_new.children.append(child_new)
        return node_new

    def get_node(self, addr):
        if len(addr) == 0:
            return self
        else:
            new_addr = addr.copy()
            child_idx = new_addr.pop(0)
            return self.children[child_idx].get_node(new_addr)

    def infer_spec(self, output, inputs):
        if self.semantics is not None:
            wire_spec = [
                       output.len == self.semantics.output.len,
                       output.min == self.semantics.output.min,
                       output.max == self.semantics.output.max,
                       output.first == self.semantics.output.first,
                       output.last == self.semantics.output.last,
                   ]
            spec = [*self.semantics.spec]
            spec_map = self.spec_map
            for i, child in enumerate(self.children):
                if child.component in LAMBDAS or child.component is None:
                    continue
                else:
                    child_wire_spec, child_spec, child_spec_map = child.infer_spec(self.semantics.inputs[i],
                                                                  inputs)
                    wire_spec += child_wire_spec
                    spec += child_spec
                    spec_map = {**spec_map, **child_spec_map}
            return wire_spec, spec, spec_map
        elif type(self.component) == Variable:
            x = inputs[self.component.index]
            spec = [
                x.len == output.len,
                x.min == output.min,
                x.max == output.max,
                x.first == output.first,
                x.last == output.last,
            ]
            spec_map = dict()
            for s in spec:
                spec_map[s] = (self, self.component)
            return list(), spec, spec_map
        else:
            return list(), list(), dict()

    def clear(self):
        self.component = None
        self.children = []
        self.semantics = None
        self.spec_map = dict()

    def run(self, inputs):
        if self.component in LAMBDAS:
            return self.component
        elif type(self.component) == Variable:
            value = inputs[self.component.index]
            t = INT if type(value) == int else LIST
            return Value(inputs[self.component.index], t)
        else:
            f_inputs = list()
            for child in self.children:
                f_inputs.append(child.run(inputs))
            return self.component(*f_inputs)

    def __str__(self):
        if self.component is None:
            return '?'
        elif type(self.component) == Variable:
            return str(self.component._name)
        else:
            text = str(self.component)
            if len(self.children) > 0:
                text += '('
                text += ','.join([str(child) for child in self.children])
                text += ')'
            return text
