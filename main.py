from sympy import *
from sympy.solvers.inequalities import reduce_rational_inequalities
import copy
from sympy import symbols
from z3 import Solver, sat
from z3 import Int, Real, Sqrt
from sympy.core import Mul, Expr, Add, Pow, Symbol, Number

class Piece:

    def __init__(self, f, P):
        self.f = f
        self.P = P

    def __repr__(self):
        return '({0} if {1})'.format(self.f, self.P)

class PiecewiseExpression:

    def __init__(self):
        self.pieces = []

    def add_context(self, c):
        for p in self.pieces:
            p.P = p.P + c

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

# Build the identity matrix
r, c = symbols("r c")
N = symbols("N")

Bnds = [1 <= r, r <= N, 1 <= c, c <= N]
I = PiecewiseExpression()
I.add_piece(nsimplify(0), Bnds + [r < c])
I.add_piece(nsimplify(0), Bnds + [r > c])
I.add_piece(nsimplify(1), Bnds + [Eq(r, c)])

print(I)

def sympy_to_z3(sympy_var_list, sympy_exp):
    'convert a sympy expression to a z3 expression. This returns (z3_vars, z3_expression)'

    z3_vars = []
    z3_var_map = {}

    for var in sympy_var_list:
        # print('var: ', var)
        name = var.name
        z3_var = Int(name)
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

def cull_pieces(I):
    I_culled = PiecewiseExpression()
    for p in I.pieces:
        varlist = []
        for cs in p.P:
            for sym in cs.free_symbols:
                varlist.append(sym)
        # [N, r, c, k]
        s = Solver()
        for cs in p.P:
            # print(cs)

            expr = sympy_to_z3([N, r, c, k], cs.lhs - cs.rhs)[1]
            if isinstance(cs, Equality):
                s.add(expr == 0)
            elif isinstance(cs, StrictGreaterThan):
                s.add(expr > 0)
            elif isinstance(cs, StrictLessThan):
                s.add(expr < 0)
            elif isinstance(cs, LessThan):
                s.add(expr <= 0)
            elif isinstance(cs, GreaterThan):
                s.add(expr >= 0)
            else:
                print('\tunrecognized comparator')
                assert(False)

        result = s.check()

        if result == sat:
            m = s.model()
            print ("SAT: {}".format(m))
            I_culled.add_piece(copy.deepcopy(p.f), copy.deepcopy(p.P))
        else:
            print ("UNSAT")

    return I_culled

print(cull_pieces(I))

def product(A, B):
    r, c, k = symbols("r c k")
    Il = A.subs(c, k)
    Ir = B.subs(r, k)

    prod = pwmul(Il, Ir)

    orders = [[[r], [c]], [[c], [r]], [[r, c]]]
    constraints = [[Eq(k, c)], [Eq(k, r)]]

    matrix_product = PiecewiseExpression()
    for order in orders:
        print('####### Checking order')
        order_cs = []
        for gp in order:
            for i in gp:
                for j in gp:
                    if i != j:
                        order_cs.append(Eq(i, j))
        for i in range(len(order) - 1):
            order_cs.append(order[i][0] < order[i + 1][0])

        k_ranges = []
        rc_sums = 0
        for gp in order:
            k_ranges.append([Eq(k, gp[0])])
        for i in range(len(order) - 1):
            kl = k >= order[i][0] + 1
            ku = k < order[i + 1][0]
            k_ranges.append([kl, ku])
        for cc in k_ranges:
            print('------- Checking order:', order, 'with constraints:', cc)
            pr = copy.deepcopy(prod)
            pr.add_context(order_cs + cc)

            prod_culled = cull_pieces(pr)
            print('Culled prod')
            print(prod_culled)
            print('Prod culled pieces:', len(prod_culled.pieces))
            assert(len(prod_culled.pieces) == 1)
            kl = cc[0].rhs
            ku = cc[0].rhs
            if len(cc) == 2:
                ku = cc[1].rhs
            rc_sums = simplify(rc_sums + Sum(prod_culled.pieces[0].f, (k, kl, ku)))

        matrix_product.add_piece(rc_sums, order_cs)
    return matrix_product

matprod = product(I, I)
print(matprod)

