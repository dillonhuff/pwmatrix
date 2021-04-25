from sympy import *
from language import *

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

res = left_reduce(App(ss, [7]))
print('res:',res)

ss = App(ConcreteSum(), [1, 7, f])
print(ss)

fss = concretify_sum(res)

print('Concrete')
for p in fss.pieces:
    print(p)
    print()

res = execute(fss, [])
assert(res == 28)

f = Function("f")
r, c = symbols("r c")
N = symbols("N")
Bnds = [1 <= r, r <= N, 1 <= c, c <= N]
UpperTriangular = PiecewiseExpression()
UpperTriangular.add_piece(nsimplify(f(r, c)), Bnds + [r <= c])
UpperTriangular.add_piece(nsimplify(0), Bnds + [r > c])

C = Function("C")
R = Function("R")
P = PiecewiseExpression()
P.add_piece(nsimplify(0), Bnds + [C(r) > c])
P.add_piece(nsimplify(0), Bnds + [C(r) < c])
P.add_piece(nsimplify(1), Bnds + [Eq(C(r), c)])

I = PiecewiseExpression()
I.add_piece(nsimplify(0), Bnds + [r < c])
I.add_piece(nsimplify(0), Bnds + [r > c])
I.add_piece(nsimplify(1), Bnds + [Eq(r, c)])

Dense = PiecewiseExpression()
Dense.add_piece(f(r, c), Bnds)

# ip = cull_pieces(mutate_after(evaluate_product(Dense, P), lambda x: simplify_sum(x) if isinstance(x, App) and isinstance(x.f, ConcreteSum) else x))
# print('--- Pieces of permutation matrix product...')
# for p in ip.pieces:
    # print(p)
    # print()

# ip = cull_pieces(mutate_after(evaluate_product(P, Dense), lambda x: simplify_sum(x) if isinstance(x, App) and isinstance(x.f, ConcreteSum) else x))
# print('--- Pieces of permutation matrix product...')
# for p in ip.pieces:
    # print(p)
    # print()

# evaluate_product(I, I)
print()
i0, j0, t = symbols("i0 j0 t")

le = Lambda([i0], Set([j0], [1 <= j0, j0 <= i0]))
print(le)

f = Lambda([t], t)
print(f)

i = symbols("i")
ss = Lambda([i], App(SymSum(), [App(le, [i]), f]))

print('lam:', ss)


res = left_reduce(App(ss, ['i']))
print('res:',res)
# assert(false)

r = concretify_sum(res)
print(r)

k0 = symbols("k0")
l = symbols("l")
le = Lambda([i0, k0], Set([j0], [k0 <= j0, j0 <= i0]))
ss = Lambda([i, l], App(SymSum(), [App(le, [i, l]), f]))

print('lam:', ss)


res = left_reduce(App(ss, [i, l]))
print('res:',res)

r = concretify_sum(res)
print('concrete results', r)

r, c = symbols("r c")
N = symbols("N")
# ip = cull_pieces(mutate_after(evaluate_product(I, UpperTriangular), lambda x: simplify_sum(x) if isinstance(x, App) and isinstance(x.f, ConcreteSum) else x))

# print(ip)
# print()
# print('--- Pieces...')
# for p in ip.pieces:
    # print(p)
    # print()


Banded = PiecewiseExpression()
B = symbols("B")
b = Function("b")
Banded.add_piece(b(r, c), Bnds + [1 <= B, B <= N, r - c <= B, -r + c <= B])

ds = Function("ds")
ts = Function("ts")
UpperBidiagonal = PiecewiseExpression()
UpperBidiagonal.add_piece(ds(r), Bnds + [Eq(r, c)])
UpperBidiagonal.add_piece(ts(r), Bnds + [Eq(r - 1, c)])

UpperBidiagonalT= PiecewiseExpression()
UpperBidiagonalT.add_piece(ds(c), Bnds + [Eq(c, r)])
UpperBidiagonalT.add_piece(ts(c), Bnds + [Eq(c - 1, r)])

ip = mutate_after(evaluate_product(UpperBidiagonalT, UpperBidiagonal), lambda x: simplify_sum(x) if isinstance(x, App) and isinstance(x.f, ConcreteSum) else x)
ip = mutate_after(ip, lambda x: cull_pieces(x) if isinstance(x, PiecewiseExpression) else x)
print(ip)
print()

merged = merge_pieces(ip) # App(SymPlus(), sums)
print('ip =', ip)

for k in merged.vs:
    print('--- # of Pieces = {}'.format(len(k.pieces)))
    for p in k.pieces:
        print(p)
        print()
assert(False)

ip11 = execute(Lambda([N, r, c], ip), [10, 1, 1])
merged11 = execute(Lambda([N, r, c], merged), [10, 1, 1])
print('ip11     =', ip11)
print('merged11 =', merged11) 
assert(ip11 == merged11)

ip43 = execute(Lambda([N, r, c], ip), [10, 4, 3])
merged43 = execute(Lambda([N, r, c], merged), [10, 4, 3])
assert(ip43 == merged43)

ip34 = execute(Lambda([N, r, c], ip), [10, 3, 4])
merged34 = execute(Lambda([N, r, c], merged), [10, 3, 4])
assert(ip34 == merged34)

print('Banded', Banded)

ip = cull_pieces(mutate_after(evaluate_product(Banded, Dense), lambda x: simplify_sum(x) if isinstance(x, App) and isinstance(x.f, ConcreteSum) else x))

print(ip)
print()
print('--- Pieces...')
for p in ip.pieces:
    print(p)
    print()

ip = ip.subs('B', 3)
# ip = ip.subs('N', 100)
ip = cull_pieces(ip)

print()
print('--- Pieces...')
for p in ip.pieces:
    print(p)
    print()

