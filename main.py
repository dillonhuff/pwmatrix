from sympy import *
import copy

# class Piece:

    # def __init__(self, f, P):
        # self.f = f
        # self.P = P

    # def __repr__(self):
        # return '({0} if {1})'.format(self.f, self.P)

# class PiecewiseExpression:

    # def __init__(self):
        # self.pieces = []

    # def subs(self, x, y):
        # rp = copy.deepcopy(self)
        # for p in rp.pieces:
            # p.f = p.f.subs(x, y)
            # cs = []
            # for cc in p.P:
                # cs.append(cc.subs(x, y))
            # p.P = cs
        # return rp

    # def add_piece(self, f, p):
        # self.pieces.append(Piece(f, p))

    # def __repr__(self):
        # ss = '[{0}]'.format(self.pieces)
        # return ss

# def compose_pointwise(op, f, g):
    # composed = []
    # for fp in f.pieces:
        # for gp in g.pieces:
            # composed.pieces.append(Piece(op(fp.f, gp.f), fp.P + gp.P))
    # return composed

# def pwmul(a, b):
    # return compose_pointwise(lambda x, y: x*y, a, b)

x, k = symbols("x k")

# pwf = Piecewise()

# pwf.add_piece(0, [2*k > x])
# pwf.add_piece(1, [2*k <= x])

# p0 = PiecewiseExpression()
# p0.add_piece(5, [k > x])
# p0.add_piece(7, [k <= x])

# print(pwf)

# print(compose_pointwise(lambda x, y: x*y, pwf, p0))


# Build a identity matrix
r, c = symbols("r c")
N = symbols("N")

Bnds = And(1 <= r, r <= N, 1 <= c, c <= N)
print(Bnds)

I = Piecewise((nsimplify(0), And(Bnds, r < c)), (nsimplify(0), And(Bnds, r < c)), (nsimplify(1), And(Bnds, Eq(r, c))))

print(I)

Il = I.subs(c, k)
Ir = I.subs(r, k)

print(Il)
print(Ir)

prod = piecewise_fold(Il*Ir)
print(prod)

# print(prod.as_expr_set_pairs())
# print(prod._intervals(k))
