from sympy import *
from sympy.solvers.inequalities import reduce_rational_inequalities
import copy
from sympy import symbols
from z3 import Solver, sat
from z3 import Int, Real, Sqrt
from sympy.core import Mul, Expr, Add, Pow, Symbol, Number
import islpy as isl

class Piece:

    def __init__(self, f, P):
        self.f = f
        self.P = P

    def __repr__(self):
        return '({0} if {1})'.format(self.f, self.P)

    @property
    def variables(self):
        syms = set()
        for s in self.f.variables:
            syms.add(s)
        for cs in self.P:
            for cc in cs.variables:
                print(cc)
                syms.add(cc)
        return syms

    @property
    def free_symbols(self):
        syms = set()
        for s in self.f.free_symbols:
            syms.add(s)
        for cs in self.P:
            for cc in cs.free_symbols:
                print(cc)
                syms.add(cc)
        return syms


class PiecewiseExpression:

    def __init__(self):
        self.pieces = []

    @property
    def variables(self):
        syms = set()
        for p in self.pieces:
            print(p)
            for s in p.variables:
                syms.add(s)
        return syms

    @property
    def free_symbols(self):
        syms = set()
        for p in self.pieces:
            print(p)
            for s in p.free_symbols:
                syms.add(s)
        return syms

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

    def to_sympy(self):
        symps = []
        for p in self.pieces:
            cond = sympify(True)
            for cs in p.P:
                cond = cond & cs
            print('cond = ', cond)
            symps.append((p.f, cond))
        return Piecewise(*symps)

def compose_pointwise(op, f, g):
    composed = PiecewiseExpression()
    for fp in f.pieces:
        for gp in g.pieces:
            composed.pieces.append(Piece(op(fp.f, gp.f), fp.P + gp.P))
    return composed

def pwmul(a, b):
    return compose_pointwise(lambda x, y: x*y, a, b)

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


print(cull_pieces(I))

def place_t_in_order(t, term_order):
    ords = []
    # Create a group where t is in each equivalence class
    for i in range(len(term_order)):
        cpyord = copy.deepcopy(term_order)
        cpyord[i].append(t)
        ords.append(cpyord)

    # Create a group where t is between each equivalence class
    for i in range(len(term_order) + 1):
        cpyord = copy.deepcopy(term_order)
        cpyord.insert(i, [t])
        ords.append(cpyord)
    return ords

def enumerate_orders(terms):
    if len(terms) == 0:
        return []
    if len(terms) == 1:
        return [[[terms[0]]]]

    orders = []
    t = terms[0]
    other_ords = enumerate_orders(terms[1:])
    for other_ord in other_ords:
        sub_ords = place_t_in_order(t, other_ord)
        orders = orders + sub_ords

    return orders

print(enumerate_orders([r, c]))
assert(len(enumerate_orders([r, c])) == 3)

def product(A, B):
    r, c, k = symbols("r c k")
    Il = A.subs(c, k)
    Ir = B.subs(r, k)

    prod = pwmul(Il, Ir)

    terms_to_order = [r, c]

    orders = enumerate_orders(terms_to_order)
    # constraints = [[Eq(k, c)], [Eq(k, r)]]

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
        for gp in order:
            k_ranges.append([Eq(k, gp[0])])
        for i in range(len(order) - 1):
            kl = k >= order[i][0] + 1
            ku = k < order[i + 1][0]
            k_ranges.append([kl, ku])

        # Compute the sum terms in k
        rc_sums = 0
        sigma_terms = []
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
            # TODO: Should have the sum on the outside
            rc_sums = simplify(rc_sums + Sum(prod_culled.pieces[0].f, (k, kl, ku)))
            sigma_terms.append((prod_culled, (k, kl, ku)))

        print('\nsigma terms:', sigma_terms)
        rcs = 0
        for s in sigma_terms:
            rcs = rcs + Sum(s[0].to_sympy(), s[1]).doit()
        print(rcs)
        matrix_product.add_piece(rcs, order_cs) #rc_sums, order_cs + prod_culled.pieces[0].P)
    return matrix_product

Dense = PiecewiseExpression()
f = Function("f")
Dense.add_piece(nsimplify(f(r, c)), Bnds)

Symmetric = PiecewiseExpression()
Symmetric.add_piece(nsimplify(f(r, c)), Bnds + [r <= c])
Symmetric.add_piece(nsimplify(f(c, r)), Bnds + [r > c])

UpperTriangular = PiecewiseExpression()
UpperTriangular.add_piece(nsimplify(f(r, c)), Bnds + [r <= c])
UpperTriangular.add_piece(nsimplify(0), Bnds + [r > c])

# matprod = product(I, Dense)
matprod = product(UpperTriangular, UpperTriangular)
print(matprod)

print('---pieces')
for p in matprod.pieces:
    print(p)
    # print(ccode(p.f))
    print()

def codegen(pwf, constant_values, variable_domains):
    ss = 'void realize_pwf({0})'.format(pwf.free_symbols) + '{\n'
    ss += '}\n'
    return ss

print('----- Codegen')
print(codegen(matprod, [], []))
