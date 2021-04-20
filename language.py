from sympy import *
import copy

class Lambda:

    def __init__(self, vs, f):
        self.vs = vs
        self.f = f

    def __repr__(self):
        return "\u03BB {0}. {1}".format(self.vs, self.f)

class Set:

    def __init__(self, vs, constraints):
        self.vs = vs
        self.constraints = constraints

    def __repr__(self):
        return "{" + str(self.vs) + " | " + str(self.constraints) + "}"

class App:

    def __init__(self, f, vs):
        self.f = f
        self.vs = vs

class SymSum:

    def __init__(self, domain, f):
        self.domain = domain
        self.f = f

class ConcreteSum:

    def __init__(self, k, start, end, f):
        self.k = k
        self.start = start
        self.end = end
        self.f = f

class Op:

    def __init__(self, name, args):
        self.name = name
        self.args = args

i0, j0 = symbols("i0 j0")

le = Lambda([i0], Set([j0], [1 <= i0, i0 <= j0]))
print(le)


