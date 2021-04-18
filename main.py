from sympy import *
from sympy.solvers.inequalities import reduce_rational_inequalities
import copy

class Piece:

    def __init__(self, f, P):
        self.f = f
        self.P = P

    def __repr__(self):
        return '({0} if {1})'.format(self.f, self.P)

class PiecewiseExpression:

    def __init__(self):
        self.pieces = []

    def subs(self, x, y):
        rp = copy.deepcopy(self)
        for p in rp.pieces:
            p.f = p.f.subs(x, y)
            cs = []
            for cc in p.P:
                cs.append(cc.subs(x, y))
            p.P = cs
        return rp

    def add_piece(self, f, p):
        self.pieces.append(Piece(f, p))

    def __repr__(self):
        ss = '[{0}]'.format(self.pieces)
        return ss

def compose_pointwise(op, f, g):
    composed = PiecewiseExpression()
    for fp in f.pieces:
        for gp in g.pieces:
            composed.pieces.append(Piece(op(fp.f, gp.f), fp.P + gp.P))
    return composed

def pwmul(a, b):
    return compose_pointwise(lambda x, y: x*y, a, b)

x, k = symbols("x k")

pwf = PiecewiseExpression()

pwf.add_piece(0, [2*k > x])
pwf.add_piece(1, [2*k <= x])

p0 = PiecewiseExpression()
p0.add_piece(5, [k > x])
p0.add_piece(7, [k <= x])

print(pwf)

print(compose_pointwise(lambda x, y: x*y, pwf, p0))


# Build a identity matrix
r, c = symbols("r c")
N = symbols("N")

Bnds = [1 <= r, r <= N, 1 <= c, c <= N]
I = PiecewiseExpression()
I.add_piece(nsimplify(0), Bnds + [r < c])
I.add_piece(nsimplify(0), Bnds + [r > c])
I.add_piece(nsimplify(0), Bnds + [Eq(r, c)])

print(I)
# Bnds = And(1 <= r, r <= N, 1 <= c, c <= N)
# print(Bnds)

# I = Piecewise((nsimplify(0), And(Bnds, r < c)), (nsimplify(0), And(Bnds, r < c)), (nsimplify(1), And(Bnds, Eq(r, c))))

# print(I)

Il = I.subs(c, k)
Ir = I.subs(r, k)



# print(Il)
# print(Ir)

prod = pwmul(Il, Ir)
print('Prod...')
print(prod)

coeffs = set()
lines = set()
for p in prod.pieces:
    for c in p.P:
        print(c)
        val = c.rhs - c.lhs
        print('\tval =', val)
        print('\tcoeff k =', val.coeff(k))
        valsimp = val + -1*val.coeff(k)*k
        lines.add((val.coeff(k)*k, valsimp))
        print('\tnormed:', valsimp)
        coeffs.add(valsimp)

print(coeffs)
print('Lines...')
for l in lines:
    print (l)
        # print('\t', Rel(c.lhs, c.rhs, c.rop))
        # print(simplify(c))
        # print(solveset(c, k, domain=S.Reals))

        # c.lhs = c.lhs - c.rhs
        # c.rhs = 0
        # print('\tnormed:', normed)
        # if k in c.free_symbols:
            # print('\tcontains k')
        # print(reduce_rational_inequalities([[c]], k))
        # print(solve(c, k, domain='ZZ'))

from z3 import Real, Sqrt
from sympy.core import Mul, Expr, Add, Pow, Symbol, Number

def sympy_to_z3(sympy_var_list, sympy_exp):
    'convert a sympy expression to a z3 expression. This returns (z3_vars, z3_expression)'

    z3_vars = []
    z3_var_map = {}

    for var in sympy_var_list:
        name = var.name
        z3_var = Real(name)
        z3_var_map[name] = z3_var
        z3_vars.append(z3_var)

    result_exp = _sympy_to_z3_rec(z3_var_map, sympy_exp)

    return z3_vars, result_exp

def _sympy_to_z3_rec(var_map, e):
    'recursive call for sympy_to_z3()'

    rv = None

    if not isinstance(e, Expr):
        raise RuntimeError("Expected sympy Expr: " + repr(e))

    if isinstance(e, Symbol):
        rv = var_map.get(e.name)

        if rv == None:
            raise RuntimeError("No var was corresponds to symbol '" + str(e) + "'")

    elif isinstance(e, Number):
        rv = float(e)
    elif isinstance(e, Mul):
        rv = _sympy_to_z3_rec(var_map, e.args[0])

        for child in e.args[1:]:
            rv *= _sympy_to_z3_rec(var_map, child)
    elif isinstance(e, Add):
        rv = _sympy_to_z3_rec(var_map, e.args[0])

        for child in e.args[1:]:
            rv += _sympy_to_z3_rec(var_map, child)
    elif isinstance(e, Pow):
        term = _sympy_to_z3_rec(var_map, e.args[0])
        exponent = _sympy_to_z3_rec(var_map, e.args[1])

        if exponent == 0.5:
            # sqrt
            rv = Sqrt(term)
        else:
            rv = term**exponent

    if rv == None:
        raise RuntimeError("Type '" + str(type(e)) + "' is not yet implemented for convertion to a z3 expresion. " + \
                            "Subexpression was '" + str(e) + "'.")

    return rv

# print(solve([1 <= r + k], k, domain='ZZ'))

# print(prod.as_expr_set_pairs())
# print(prod._intervals(k))
from sympy import symbols
from z3 import Solver, sat

var_list = x, y = symbols("x y")

sympy_exp = -x**2 + y + 1
z3_vars, z3_exp = sympy_to_z3(var_list, sympy_exp)

z3_x = z3_vars[0]
z3_y = z3_vars[1]

s = Solver()
s.add(z3_exp == 0) # add a constraint with converted expression
s.add(z3_y >= 0) # add an extra constraint

result = s.check()

if result == sat:
    m = s.model()

    print ("SAT at x={}, y={}".format(m[z3_x], m[z3_y]))
else:
    print ("UNSAT")
