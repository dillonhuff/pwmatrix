from sympy import *
import copy

def container_position(val, l):
    i = 0
    for container in l:
        if val in container:
            return i
        i += 1
    print('Error: No element contains {0} in {1}'.format(val, l))
    assert(False)

def mutate_after(k, M):
    if hasattr(k, 'mutate_after'):
        return k.mutate_after(M)
    return k

def compose_pointwise(op, f, g):
    composed = PiecewiseExpression()
    for fp in f.pieces:
        for gp in g.pieces:
            operator = op(fp.f, gp.f)
            if operator != 0:
                composed.pieces.append(Piece(op(fp.f, gp.f), fp.P + gp.P))
    return composed

def pwmul(a, b):
    return compose_pointwise(lambda x, y: x*y, a, b)

def scale(scalar, cs):
    print('\t\t\tscaling {0} by {1}'.format(cs, scalar))
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
        if isinstance(vs, list):
            self.vs = vs
        else:
            self.vs = [vs]
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

    def mutate_after(self, M):
        ff = mutate_after(self.f, M)
        fP = mutate_after(self.P, M)
        return M(Piece(ff, fP))

    def __repr__(self):
        return '{0} if {1}'.format(self.f, self.P)

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

    def mutate_after(self, M):
        cpy = PiecewiseExpression()
        for p in self.pieces:
            mp = mutate_after(p, M)
            cpy.add_piece(mp.f, mp.P)
        return M(cpy)

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
        ss = '{' + '{0}'.format(', '.join(list(map(lambda x: str(x), self.pieces)))) + '}'
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

def simplify_pieces(ss):
    simplified = copy.deepcopy(ss)
    for p in simplified.pieces:
        print('\tsimplifying:', p)
        fr = set()
        for cs in p.P:
            ss = simplify(cs.doit())
            if ss != True:
                fr.add(ss)
        p.P = list(fr)
    return simplified

def extract_unconditional_expression(simplified):
    if len(simplified.pieces) == 1 and len(simplified.pieces[0].P) == 0:
        return simplified.pieces[0].f
    return simplified

def distribute_piece(pwf):
    assert(isinstance(pwf, PiecewiseExpression))
    if len(pwf.pieces) == 1:
        if isinstance(pwf.pieces[0].f, PiecewiseExpression):
            pushed = copy.deepcopy(pwf.pieces[0].f)
            pushed.add_context(pwf.pieces[0].P)
            return pushed
    return pwf

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
    constraints_no_eq = set()
    for cs in constraints:
        if isinstance(cs, Equality):
            constraints_no_eq.add(cs.lhs >= cs.rhs)
            constraints_no_eq.add(cs.lhs <= cs.rhs)
        else:
            constraints_no_eq.add(cs)
    normalized = set()
    for cs in constraints_no_eq:
        if cs == True:
            continue
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
            print('\tunrecognized comparator in constraint:', cs)
            assert(False)

    print(normalized)

    print('moving sum var to RHS...')
    var_rhs = set()
    for cs in normalized:
        expr = cs.lhs - cs.rhs
        # no_var = -1*expr.coeff(var)*(expr + -1*expr.coeff(var)*var)
        print('\t:', cs)
        print('\t:', expr)
        if isinstance(cs, Equality):
            var_rhs.add(Eq(expr, 0))
        elif isinstance(cs, LessThan):
            var_rhs.add(expr <= 0)
        elif isinstance(cs, GreaterThan):
            var_rhs.add(expr >= 0)
        else:
            print('\tunrecognized comparator')
            assert(False)
        print('\tvar_rhs', var_rhs)

    print('var rhs:', var_rhs)

    scaled_coeffs = set()
    for cs in var_rhs:
        if cs.lhs.coeff(var) == 0:
            scaled_coeffs.add(cs)
        else:
            print('\tscaling:', cs)
            scaled_cs = scale(cs.lhs.coeff(var), cs)
            print('\t\tscaled_cs', scaled_cs)
            scaled_coeffs.add(scaled_cs)

    print('scaled', scaled_coeffs)
    isolated = set()
    for cs in scaled_coeffs:
        if cs == True:
            continue
        if cs.lhs.coeff(var) == 0:
            isolated.add(cs)
        else:
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
        if cs.rhs.coeff(var) == 0:
            auxiliary.append(cs)
        else:
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

def fm_domain_decomposition(k, all_constraints):
    equalities, upper_bounds, lower_bounds, auxiliary_constraints = separate_constraints(k, all_constraints)
    print('eq:', equalities)
    print('ub:', upper_bounds)
    print('lb:', lower_bounds)
    print('ax:', auxiliary_constraints)
    assert(len(equalities) == 0)

    terms_to_order = set()
    for b in upper_bounds:
        terms_to_order.add(b.lhs)
    for b in lower_bounds:
        terms_to_order.add(b.lhs)
    print('to order', terms_to_order)
    orders = enumerate_orders(list(terms_to_order))
    lbs = set()
    for l in lower_bounds:
        lbs.add(l.lhs)
    ubs = set()
    for l in upper_bounds:
        ubs.add(l.lhs)
    print('\norders:', orders)
    print('\tub:', ubs)
    print('\tlb:', lbs)

    domain_decomposition = []
    for order in orders:
        print('\tOrder:', order)
        least_upper_bound_pos = min(map(lambda x: container_position(x, order), ubs))
        greatest_lower_bound_pos = max(map(lambda x: container_position(x, order), lbs))

        least_upper_bound_representative = order[least_upper_bound_pos][0]
        greatest_lower_bound_representative = order[greatest_lower_bound_pos][0]
        if least_upper_bound_pos == greatest_lower_bound_pos:
            print('\t\tk is a point {0}'.format(least_upper_bound_representative))
            domain_decomposition.append([least_upper_bound_representative, least_upper_bound_representative, order_to_constraints(order) + auxiliary_constraints])
        elif least_upper_bound_pos > greatest_lower_bound_pos:
            print('\t\tk is an interval [{0}, {1}]'.format(greatest_lower_bound_representative, least_upper_bound_representative))
            domain_decomposition.append([greatest_lower_bound_representative, least_upper_bound_representative, order_to_constraints(order) + auxiliary_constraints])
        else:
            print('\t\tk is empty')
    # assert(False)

    # domain_decomposition = []
    # for l in lower_bounds:
        # l_constraints = []
        # for k in lower_bounds:
            # l_constraints.append(k.lhs <= l.lhs)
        # for u in upper_bounds:
            # u_constraints = []
            # for k in upper_bounds:
                # u_constraints.append(k.lhs >= u.lhs)

            # domain_decomposition.append([l.lhs, u.lhs, auxiliary_constraints + l_constraints + u_constraints + [l.lhs <= u.lhs]])
    return domain_decomposition

def concretify_sum(symsum):
    assert(isinstance(symsum, App))
    assert(isinstance(symsum.f, SymSum))
    assert(len(symsum.vs) == 2)

    domain = symsum.vs[0]
    assert(isinstance(domain, Set))
    assert(len(domain.vs) == 1)

    k = domain.vs[0]

    all_constraints = copy.deepcopy(domain.constraints)
    domain_decomposition = fm_domain_decomposition(k, all_constraints)
    piecewise_sums = PiecewiseExpression()
    for part in domain_decomposition:
        piecewise_sums.add_piece(App(ConcreteSum(), [part[0], part[1], symsum.vs[1]]), part[2])

    print(piecewise_sums)
    return piecewise_sums

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

def separate_sum_of_pieces(ss):
    assert(isinstance(ss, App))
    assert(isinstance(ss.f, SymSum))

    domain = ss.vs[0]
    func = ss.vs[1]
    print('func:', func)
    assert(isinstance(func, Lambda))
    assert(len(func.vs) == 1)

    var = func.vs[0]
    func = func.f
    sepsum = []
    for p in func.pieces:
        if p.f != 0:
            sepsum.append(App(SymSum(), [Set(domain.vs, list(domain.constraints) + list(p.P)), Lambda([var], p.f)]))
    if len(sepsum) == 1:
        return sepsum[0]
    return App('+', sepsum)

def product(A, B):
    r, c, k = symbols("r c k")
    Il = A.subs(c, k)
    Ir = B.subs(r, k)

    prod = simplify_pieces(pwmul(Il, Ir))

    ss = Set([k], [sympify(True)])
    return App(SymSum(), [ss, Lambda(k, prod)])

def evaluate_product(A, B):
    ip = product(A, B)
    print('\nA*B:', ip)

    sepsum = separate_sum_of_pieces(ip)
    print('separated sum:', sepsum)

    sepsum = concretify_sum(sepsum)
    print('Concrete:', sepsum)
    simplified = simplify_pieces(extract_unconditional_expression(sepsum))
    simplified = distribute_piece(mutate_after(simplified, lambda x: simplify_pieces(x) if isinstance(x, PiecewiseExpression) else x))
    print('Concrete after simplification:', simplified)
    return simplified

Bnds = [1 <= r, r <= N, 1 <= c, c <= N]
I = PiecewiseExpression()
I.add_piece(nsimplify(0), Bnds + [r < c])
I.add_piece(nsimplify(0), Bnds + [r > c])
I.add_piece(nsimplify(1), Bnds + [Eq(r, c)])


evaluate_product(I, I)
print()
# print('I:', I)
# ip = product(I, I)
# print('\nI*I:', ip)


# sepsum = separate_sum_of_pieces(ip)
# print('separated sum:', sepsum)

# sepsum = concretify_sum(sepsum)
# print('Concrete:', sepsum)
# simplified = simplify_pieces(extract_unconditional_expression(sepsum))
# simplified = distribute_piece(mutate_after(simplified, lambda x: simplify_pieces(x) if isinstance(x, PiecewiseExpression) else x))
# print('Concrete after simplification:', simplified)
# assert(False)

f = Function("f")
UpperTriangular = PiecewiseExpression()
UpperTriangular.add_piece(nsimplify(f(r, c)), Bnds + [r <= c])
UpperTriangular.add_piece(nsimplify(0), Bnds + [r > c])

# ip = product(I, UpperTriangular)
print(evaluate_product(I, UpperTriangular))
assert(False)

# ip = product(UpperTriangular, UpperTriangular)
# ip = product(I, I)
sepsum = separate_sum_of_pieces(ip)
print('separated sum:', sepsum)

simplified = concretify_sum(sepsum)
print('# of simplified pieces = ', len(simplified.pieces))

simplified = simplify_pieces(simplified)

simplified = simplify_pieces(extract_unconditional_expression(simplified))
simplified = distribute_piece(mutate_after(simplified, lambda x: simplify_pieces(x) if isinstance(x, PiecewiseExpression) else x))
print(simplified)

