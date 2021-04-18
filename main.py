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
for p in prod.pieces:
    for c in p.P:
        print(c)
        val = c.rhs - c.lhs
        print('\tval =', val)
        print('\tcoeff k =', val.coeff(k))
        val = val + -1*val.coeff(k)*k
        print('\tnormed:', val)
        coeffs.add(val)

print(coeffs)
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

# print(solve([1 <= r + k], k, domain='ZZ'))

# print(prod.as_expr_set_pairs())
# print(prod._intervals(k))
