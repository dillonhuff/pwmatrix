from sympy import *
import copy

def substitute(target, value, expr):
    return expr.subs(target, value)

class Lambda:

    def __init__(self, vs, f):
        self.vs = vs
        self.f = f

    def __repr__(self):
        return "(\u03BB {0}. {1})".format(self.vs, self.f)

    def subs(self, target, value):
        if target in self.vs:
            return copy.deepcopy(self)
        print('Doing subs on {}'.format(self))
        return Lambda(self.vs, substitute(target, value, self.f))

class Set:

    def __init__(self, vs, constraints):
        self.vs = vs
        self.constraints = constraints

    def __repr__(self):
        return "{" + str(self.vs) + " | " + str(self.constraints) + "}"

    def subs(self, target, value):
        if target in self.vs:
            return copy.deepcopy(self)
        return Set(self.vs, list(map(lambda x: substitute(target, value, x), self.constraints)))

class App:

    def __init__(self, f, vs):
        self.f = f
        self.vs = vs

    def __repr__(self):
        return '({0}{1})'.format(self.f, self.vs)

    def subs(self, target, value):
        return App(substitute(target, value, self.f), list(map(lambda x: substitute(target, value, x), self.vs)))

class SymSum:

    def __init__(self):
        None

    def __repr__(self):
        return '\u2211'

    def subs(self, target, value):
        return self

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

def beta_reduce(expr):
    if isinstance(expr, App):
        print('Beta reducing {0}'.format(expr))
        f = expr.f
        vs = expr.vs
        if isinstance(f, Lambda):
            print('Beta reducing lambda {0}'.format(f))
            fresh = copy.deepcopy(f)
            for i in range(min(len(vs), len(f.vs))):
                var = f.vs[i]
                value = vs[i]
                fresh = substitute(var, value, f.f)
            return fresh
        else:
            return expr
    else:
        return expr

def left_reduce(expr):
    fresh = beta_reduce(expr)
    if isinstance(fresh, App):
        fresh = App(left_reduce(fresh.f), list(map(lambda v: left_reduce(v), fresh.vs)))
    return fresh

i0, j0, t = symbols("i0 j0 t")

le = Lambda([i0], Set([j0], [1 <= j0, j0 <= i0]))
print(le)

f = Lambda([t], t)
print(f)

i = symbols("i")
ss = Lambda([i], App(SymSum(), [App(le, [i]), f]))

print(ss)

print(beta_reduce(App(ss, [7])))

print(left_reduce(App(ss, [7])))
