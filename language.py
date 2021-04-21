from sympy import *
import copy

def compose_pointwise(op, f, g):
    composed = PiecewiseExpression()
    for fp in f.pieces:
        for gp in g.pieces:
            composed.pieces.append(Piece(op(fp.f, gp.f), fp.P + gp.P))
    return composed

def pwmul(a, b):
    return compose_pointwise(lambda x, y: x*y, a, b)
def scale(scalar, cs):
    is_negative = scalar < 0
    scaled_lhs = scalar*cs.lhs
    scaled_rhs = scalar*cs.rhs
    if isinstance(cs, Equality):
        return Eq(scaled_lhs, scaled_rhs)
    elif isinstance(cs, LessThan):
        if is_negative:
            return scaled_lhs >= scaled_rhs
        else:
            return scaled_lhs <= scaled_rhs
    elif isinstance(cs, GreaterThan):
        if is_negative:
            return scaled_lhs <= scaled_rhs
        else:
            return scaled_lhs >= scaled_rhs
    else:
        print('\tunrecognized comparator')
        assert(False)

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
        if self.f == '+':
            return '({0})'.format(' + '.join(list(map(lambda x: str(x), self.vs))))

        if self.f == '-' and len(self.vs) == 2:
            return '({0} - {1})'.format(self.vs[0], self.vs[1])

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

    def __init__(self):
        None

    def __repr__(self):
        return '\u2211'

    def subs(self, target, value):
        return self

class Op:

    def __init__(self, name, args):
        self.name = name
        self.args = args

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

def beta_reduce(expr):
    if isinstance(expr, App):
        print('Beta reducing {0}'.format(expr))
        f = expr.f
        vs = expr.vs
        if isinstance(f, Lambda):
            # print('Beta reducing lambda {0}'.format(f))
            fresh = copy.deepcopy(f.f)
            for i in range(min(len(vs), len(f.vs))):
                var = f.vs[i]
                value = vs[i]
                print('\treplacing {0} with {1} in {2}'.format(var, value, fresh))
                fresh = substitute(var, value, fresh)
            if len(vs) == len(f.vs):
                return fresh
            else:
                assert(False)
                return Lambda(f.vs[min(len(vs), len(f.vs)):], fresh)
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

res = left_reduce(App(ss, [7]))
print('res:',res)
# assert(False)

# lifted = PiecewiseExpression()
# lifted.add_piece(res, [True])
# print('lifted:', lifted)

ss = App(ConcreteSum(), [1, 7, f])
print(ss)

def order_to_constraints(order):
    k_ranges = []
    for gp in order:
        for k in gp:
            for l in gp:
                k_ranges.append(Eq(k, l))
    for i in range(len(order) - 1):
        prevg = order[i][0]
        nextg = order[i + 1][0]
        k_ranges.append(prevg < nextg)
    return k_ranges

def separate_constraints(var, constraints):
    normalized = set()
    for cs in constraints:
        if isinstance(cs, Equality):
            normalized.add(Eq(cs.lhs - cs.rhs, 0))
        elif isinstance(cs, StrictGreaterThan):
            normalized.add(cs.lhs - cs.rhs - 1 >= 0)
        elif isinstance(cs, StrictLessThan):
            normalized.add(cs.lhs - cs.rhs - 1 <= 0)
        elif isinstance(cs, LessThan):
            normalized.add(cs.lhs - cs.rhs <= 0)
        elif isinstance(cs, GreaterThan):
            normalized.add(cs.lhs - cs.rhs >= 0)
        else:
            print('\tunrecognized comparator')
            assert(False)

    print(normalized)

    var_rhs = set()
    for cs in normalized:
        expr = cs.lhs - cs.rhs
        # no_var = -1*expr.coeff(var)*(expr + -1*expr.coeff(var)*var)
        # print(no_var)
        if isinstance(cs, Equality):
            var_rhs.add(Eq(expr, 0))
        elif isinstance(cs, LessThan):
            var_rhs.add(expr <= 0)
        elif isinstance(cs, GreaterThan):
            var_rhs.add(expr >= 0)
        else:
            print('\tunrecognized comparator')
            assert(False)

    print('var rhs:', var_rhs)

    scaled_coeffs = set()
    for cs in var_rhs:
        scaled_coeffs.add(scale(cs.lhs.coeff(var), cs))

    print('scaled', scaled_coeffs)
    isolated = set()
    for cs in scaled_coeffs:
        if cs == True:
            continue
        assert(cs.lhs.coeff(var) == 1 and cs.rhs.coeff(var) == 0)
        if isinstance(cs, Equality):
            isolated.add(Eq(cs.lhs - var, cs.rhs - var))
        elif isinstance(cs, LessThan):
            isolated.add((cs.lhs - var <= cs.rhs - var))
        elif isinstance(cs, GreaterThan):
            isolated.add((cs.lhs - var >= cs.rhs - var))
        else:
            print('\tunrecognized comparator')
            assert(False)

    print(isolated)
    reisolated = set()
    for cs in isolated:
        reisolated.add(scale(-1, cs))

    print(reisolated)

    auxiliary = [sympify(True)]
    pre_equalities = []
    upper_bounds = []
    lower_bounds = []
    for cs in reisolated:
        assert(cs.lhs.coeff(var) == 0 and cs.rhs.coeff(var) == 1)
        if isinstance(cs, Equality):
            pre_equalities.append(cs)
        elif isinstance(cs, LessThan):
            lower_bounds.append(cs)
        elif isinstance(cs, GreaterThan):
            upper_bounds.append(cs)
        else:
            print('\tunrecognized comparator')
            assert(False)

    equalities = []
    if len(pre_equalities) > 0:
        replacement = pre_equalities[0].lhs
        equalities.append(pre_equalities[0])
        for ec in pre_equalities[1:]:
            auxiliary.append(ec.subs(var, replacement))

    return equalities, upper_bounds, lower_bounds, auxiliary

def concretify_sum(symsum):
    assert(isinstance(symsum, App))
    assert(isinstance(symsum.f, SymSum))
    assert(len(symsum.vs) == 2)

    domain = symsum.vs[0]
    assert(isinstance(domain, Set))
    assert(len(domain.vs) == 1)

    k = domain.vs[0]

    all_constraints = copy.deepcopy(domain.constraints)
    equalities, upper_bounds, lower_bounds, auxiliary_constraints = separate_constraints(k, all_constraints)
    print('eq:', equalities)
    print('ub:', upper_bounds)
    print('lb:', lower_bounds)
    print('ax:', auxiliary_constraints)

    # TODO: Check auxiliary constraints as well
    if (len(equalities) == 0):

        piecewise_sums = PiecewiseExpression()
        for l in lower_bounds:
            l_constraints = []
            for k in lower_bounds:
                l_constraints.append(k.lhs <= l.lhs)
            for u in upper_bounds:
                u_constraints = []
                for k in upper_bounds:
                    u_constraints.append(k.lhs >= u.lhs)
                piecewise_sums.add_piece(App(ConcreteSum(), [l.lhs, u.lhs, symsum.vs[1]]), l_constraints + u_constraints + [l.lhs <= u.lhs])
    else:
        assert(len(equalities) == 1)
        piecewise_sums = PiecewiseExpression()
        var_val = equalities[0].lhs
        for l in lower_bounds:
            l_constraints = []
            for k in lower_bounds:
                l_constraints.append(k.lhs <= l.lhs)
            for u in upper_bounds:
                u_constraints = []
                for k in upper_bounds:
                    u_constraints.append(k.lhs >= u.lhs)
                piecewise_sums.add_piece(substitute(var, var_val, symsum.vs[1]), l_constraints + u_constraints + [l.lhs <= u.lhs, l.lhs <= var_val, var_val <= u.lhs])
        # assert(False)

    print(piecewise_sums)

    wrapper = PiecewiseExpression()
    wrapper.add_piece(piecewise_sums, auxiliary_constraints)

    return wrapper

    # assert(False)

    # # Now: Move auxiliary constraints to a piecewise wrapper
    # # and delete them from the major set
    # # Enumerate all possible mixes of upper and lower bounds
    # # and sum over them
    # tms = set()
    # for constraint in all_constraints:
        # expr = constraint.lhs - constraint.rhs
        # if expr.coeff(k) == 0:
            # continue
        # no_k = -1*expr.coeff(k)*(expr + -1*expr.coeff(k)*k)
        # tms.add(no_k)

    # print(all_constraints)
    # assert(False)

    # terms_to_order = list(tms)
    # orders = enumerate_orders(terms_to_order)

    # print(tms)
    # print(orders)

    # sums_assuming_order = PiecewiseExpression()
    # for order in orders:
        # concrete_sums = []
        # ordera = copy.deepcopy(order)
        # # ordera.insert(0, ['-inf'])
        # # ordera.append(['inf'])
        # for i in range(len(ordera) - 1):
            # current = ordera[i][0]
            # next_g = ordera[i+1][0]
            # concrete_sums.append(App(ConcreteSum(), [current, App('-', [next_g, 1]), symsum.vs[1]]))

        # for i in range(len(ordera)):
            # next_g = ordera[i][0]
            # # concrete_sums.append(App(ConcreteSum(), [next_g, next_g, symsum.vs[1]]))
            # concrete_sums.append(beta_reduce(App(symsum.vs[1], [next_g])))
        # concrete_sum = App('+', concrete_sums)
        # # sums_assuming_order.add_piece(symsum, order)
        # sums_assuming_order.add_piece(concrete_sum, order_to_constraints(order))

    # print(sums_assuming_order)
    # return sums_assuming_order


fss = concretify_sum(res)

print('Concrete')
for p in fss.pieces:
    print(p)
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

def product(A, B):
    r, c, k = symbols("r c k")
    Il = A.subs(c, k)
    Ir = B.subs(r, k)

    prod = pwmul(Il, Ir)

    ss = Set([k], [1 <= k, k <= N])
    return App(SymSum(), [ss, prod])

Bnds = [1 <= r, r <= N, 1 <= c, c <= N]
I = PiecewiseExpression()
I.add_piece(nsimplify(0), Bnds + [r < c])
I.add_piece(nsimplify(0), Bnds + [r > c])
I.add_piece(nsimplify(1), Bnds + [Eq(r, c)])

print('I:', I)
ip = product(I, I)
print(ip)

def separate_sum_of_pieces(ss):
    assert(isinstance(ss, App))
    assert(isinstance(ss.f, SymSum))
    domain = ss.vs[0]
    func = ss.vs[1]
    if not isinstance(func, PiecewiseExpression):
        return ss
    print(ss, 'is a sum over a piecewise function')

    print('dom:', domain)
    sepsum = []
    for p in func.pieces:
        if p.f != 0:
            sepsum.append(App(SymSum(), [Set(domain.vs, list(domain.constraints) + list(p.P)), p.f]))
    if len(sepsum) == 1:
        return sepsum[0]
    return App('+', sepsum)

sepsum = separate_sum_of_pieces(ip)
print(sepsum)
print(concretify_sum(sepsum))


f = Function("f")
UpperTriangular = PiecewiseExpression()
UpperTriangular.add_piece(nsimplify(f(r, c)), Bnds + [r <= c])
UpperTriangular.add_piece(nsimplify(0), Bnds + [r > c])

ip = product(UpperTriangular, UpperTriangular)
sepsum = separate_sum_of_pieces(ip)
print(sepsum)

simplified = concretify_sum(sepsum)
for p in simplified.pieces:
    for cs in p.P:
        print(cs.doit())
print(simplified)

