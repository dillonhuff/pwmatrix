from sympy import *
import copy

# import networkx as nx

from z3 import Solver, sat
from z3 import Int, Real, Sqrt
import z3 as z3

import islpy as isl


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

    if e == True:
        return True
    if e == False:
        return False

    rv = None
    if isinstance(e, Equality):
        return _sympy_to_z3_rec(var_map, e.lhs) == _sympy_to_z3_rec(var_map, e.rhs)
    elif isinstance(e, StrictGreaterThan):
        return _sympy_to_z3_rec(var_map, e.lhs) > _sympy_to_z3_rec(var_map, e.rhs)
    elif isinstance(e, StrictLessThan):
        return _sympy_to_z3_rec(var_map, e.lhs) < _sympy_to_z3_rec(var_map, e.rhs)
    elif isinstance(e, LessThan):
        return _sympy_to_z3_rec(var_map, e.lhs) <= _sympy_to_z3_rec(var_map, e.rhs)
    elif isinstance(e, GreaterThan):
        return _sympy_to_z3_rec(var_map, e.lhs) >= _sympy_to_z3_rec(var_map, e.rhs)

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

    elif isinstance(e, Function):
        arg_list = []
        arg_type_list = []
        for arg in e.args:
            arg_type_list.append(z3.IntSort())
            arg_list.append(_sympy_to_z3_rec(var_map, arg))

        arg_type_list.append(z3.IntSort())
        F = z3.Function(e.func.name, *arg_type_list)
        # print('F = ', F)
        rv = F(*arg_list)
        # print('rv = ', rv)

    if rv == None:
        raise RuntimeError("Type '" + str(type(e)) + "' is not yet implemented for conversion to a z3 expresion. " + \
                            "Subexpression was '" + str(e) + "'.")

    return rv

def cull_pieces(I):
    # TODO: Replace with free variables in I
    # N, r, c, k = symbols("N r c k")
    I_culled = PiecewiseExpression()
    for p in I.pieces:
        varlist = []
        for cs in p.P:
            for sym in cs.free_symbols:
                varlist.append(sym)
        s = Solver()
        # print('checking: ', p.P)
        for cs in p.P:
            if cs == True:
                continue
            if cs == False:
                s.add(False)
                # assert(False)
                continue
            # print('cs = ', cs)
            expr = sympy_to_z3(list(cs.free_symbols), cs.lhs - cs.rhs)[1]
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
def simplify_sum(s):
    assert(isinstance(s, App))
    assert(isinstance(s.f, ConcreteSum))
    assert(len(s.vs) == 3)
    l = s.vs[0]
    u = s.vs[1]

    if l == u:
        return beta_reduce(App(s.vs[2], [l]))
    return s

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
    # print('Doing substitution on', expr)
    return expr.subs(target, value)

class Lambda:

    def __init__(self, vs, f):
        if isinstance(vs, list):
            self.vs = vs
        else:
            self.vs = [vs]
        self.f = f

    @property
    def free_symbols(self):
        fvs = self.f.free_symbols
        fvs = set.difference(fvs, set(self.vs))
        return fvs

    def __repr__(self):
        return "(\u03BB {0}. {1})".format(self.vs, self.f)

    def subs(self, target, value):
        if target in self.vs:
            return copy.deepcopy(self)
        # print('Doing subs on {}'.format(self))
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
        if isinstance(self.f, SymPlus):
            return '({0})'.format(' + '.join(list(map(lambda x: str(x), self.vs))))

        if self.f == '-' and len(self.vs) == 2:
            return '({0} - {1})'.format(self.vs[0], self.vs[1])

        return '({0}{1})'.format(self.f, self.vs)

    def mutate_after(self, M):
        freshf = M(self.f)
        freshargs = list(map(lambda x : mutate_after(x, M), self.vs))
        return M(App(freshf, freshargs))

    @property
    def free_symbols(self):
        fvs = set()
        fvs = set.union(fvs, free_variables(self.f))
        ls = list(map(lambda x: x.free_symbols, self.vs))
        for s in ls:
            fvs = set.union(fvs, s)
        return fvs

    def subs(self, target, value):
        # print('Doing subs on {}'.format(self))
        return App(substitute(target, value, self.f), list(map(lambda x: substitute(target, value, x), self.vs)))

class SymPlus:

    def __init__(self):
        None

    @property
    def free_symbols(self):
        return set()

    def __repr__(self):
        return '+'

    def subs(self, target, value):
        return self

class SymSum:

    def __init__(self):
        None

    @property
    def free_symbols(self):
        return set()

    def __repr__(self):
        return '\u2211'

    def subs(self, target, value):
        return self

class ConcreteSum:

    def __init__(self):
        None

    @property
    def free_symbols(self):
        return set()

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
                # print(cc)
                syms.add(cc)
        return syms

    @property
    def free_symbols(self):
        syms = set()
        for s in self.f.free_symbols:
            syms.add(s)
        for cs in self.P:
            for cc in cs.free_symbols:
                # print(cc)
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
            # print(p)
            for s in p.variables:
                syms.add(s)
        return syms


    @property
    def free_symbols(self):
        syms = set()
        for p in self.pieces:
            # print(p)
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

        f = expr.f
        vs = expr.vs

        if len(vs) == 0:
            return f

        if isinstance(f, Lambda):
            fresh = copy.deepcopy(f.f)
            for i in range(min(len(vs), len(f.vs))):
                var = f.vs[i]
                value = vs[i]
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

def reorganize_undefined_function(var, cs):
    if isinstance(cs, Equality):
        lhs = cs.lhs
        rhs = cs.rhs
        if isinstance(lhs, Function) and var in lhs.free_symbols:
            print(cs)
            assert(len(lhs.args) == 1)
            print(cs)
            to_ret = Eq(lhs.args[0], Function(lhs.func.name + '_inv')(rhs))
            print('ret:', to_ret)
            # assert(False)
            return to_ret

        elif isinstance(rhs, Function) and var in rhs.free_symbols:
            assert(len(rhs.args) == 1)
            print(cs)
            to_ret = Eq(rhs.args[0], Function(rhs.func.name + '_inv')(lhs))
            print('ret:', to_ret)
            # assert(False)
            return to_ret
        else:
            return cs
    else:
        return cs

def separate_constraints(var, constraints):
    print('separating:', constraints)
    constraints_no_eq = set()
    for cs in map(lambda x: reorganize_undefined_function(var, x), constraints):
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

    print('isolated:', isolated)
    # Check that every appearance
    # of the taret variable is on the RHS
    # of every constraint
    for cs in isolated:
        if var in cs.free_symbols:
            assert(not var in cs.lhs.free_symbols)

    reisolated = set()
    for cs in isolated:
        reisolated.add(scale(-1, cs))

    print(reisolated)

    auxiliary = [sympify(True)]
    pre_equalities = []
    upper_bounds = []
    lower_bounds = []
    for cs in reisolated:
        if not var in cs.rhs.free_symbols: # cs.rhs.coeff(var) == 0:
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

    for axc in auxiliary:
        assert(not var in axc.free_symbols)
    return equalities, upper_bounds, lower_bounds, auxiliary

def fm_domain_decomposition(k, all_constraints):
    equalities, upper_bounds, lower_bounds, auxiliary_constraints = separate_constraints(k, all_constraints)
    print('eq:', equalities)
    print('ub:', upper_bounds)
    print('lb:', lower_bounds)
    print('ax:', auxiliary_constraints)
    assert(len(equalities) == 0)
    for axc in auxiliary_constraints:
        assert(not k in axc.free_symbols)

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
    return domain_decomposition

def concretify_sum(symsum):
    print('concretifying:', symsum)

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

def free_variables(expr):
    if hasattr(expr, 'free_symbols'):
        return expr.free_symbols
    return set()

def execute_conditions(expr):
    assert(isinstance(expr, list))
    for c in expr:
        if c == False:
            return False
    return True

def execute(expr, variable_values):
    # print('Executing:', expr)
    # print('free vars:', free_variables(expr))
    assert(len(free_variables(expr)) == 0)

    reduced = beta_reduce(App(expr, variable_values))
    return evaluate_expr(reduced)

def evaluate_expr(reduced):
    assert(len(free_variables(reduced)) == 0)

    if isinstance(reduced, PiecewiseExpression):
        for p in reduced.pieces:
            if (execute_conditions(p.P)):
                return evaluate_expr(p.f)
        return 0
    elif isinstance(reduced, App):
        if isinstance(reduced.f, ConcreteSum):
            sval = 0
            start = evaluate_expr(reduced.vs[0])
            end = evaluate_expr(reduced.vs[1])
            sum_func = reduced.vs[2]
            for value in range(start, end + 1):
                sval += evaluate_expr(beta_reduce(App(sum_func, [value])))
            return sval
        elif isinstance(reduced.f, SymPlus):
            # assert(len(reduced.vs) == 2)
            sval = 0
            for arg in reduced.vs:
                print('\tadding', arg)
                sval += evaluate_expr(arg)
                print('\tsval =', sval)
            return sval
        else:
            print('Unrecongnized function:', reduced.f)
            assert(False)
        # print('Evaluating app:', reduced)
        # print('\tf = ', reduced.f)
        # print('\t\tisinstance =', isinstance(reduced.f, ConcreteSum))
        # print('\t\tisinstance =', isinstance(reduced.f, SymSum))
        #and isinstance(reduced, ConcreteSum):
        # assert(False)
    elif reduced.is_constant():
        return reduced
    else:
        print('Cannot evaluate {0}'.format(reduced))
        assert(False)
    return reduced

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
    return App(SymPlus(), sepsum)

def product(A, B):
    r, c, k = symbols("r c k")

    assert(r in free_variables(A))
    assert(not k in free_variables(A))

    assert(c in free_variables(B))
    assert(not k in free_variables(B))

    Il = A.subs(c, k)
    Ir = B.subs(r, k)

    prod = pwmul(Il, Ir)

    ss = Set([k], [sympify(True)])
    return App(SymSum(), [ss, Lambda(k, prod)])

def evaluate_product(A, B):
    ip = product(A, B)
    print('\nA*B:', ip)

    sepsum = separate_sum_of_pieces(ip)
    print('separated sum:', sepsum)

    sepsum = mutate_after(sepsum, lambda x: concretify_sum(x) if isinstance(x, App) and isinstance(x.f, SymSum) else x)
    print('Concrete:', sepsum)
    simplified = mutate_after(sepsum, lambda x: (extract_unconditional_expression(x)) if isinstance(x, PiecewiseExpression) else x)
    simplified = mutate_after(simplified, lambda x: distribute_piece(simplify_pieces(x)) if isinstance(x, PiecewiseExpression) else x)
    print('Concrete after simplification:', simplified)
    return simplified


def is_concrete_sum(f):
    if not isinstance(f, App):
        return False
    if isinstance(f.f, ConcreteSum):
        return True

def can_merge_into(p0, p1):
    if is_concrete_sum(p0.f) != is_concrete_sum(p1.f):
        return False

    if is_concrete_sum(p0.f) and is_concrete_sum(p1.f):
        return p0.f == p1.f
        # f0expr = p0.f.vs[2].f
        # f0lb = p0.f.vs[0]
        # f0ub = p0.f.vs[1]

        # f1expr = p1.f.vs[2].f
        # f1lb = p1.f.vs[0]
        # f1ub = p1.f.vs[1]

        # print('f0 expr:', f0expr)
        # print('f1 expr:', f1expr)

        # f0 = sympy_to_z3(list(f0expr.free_symbols), f0expr)[1]
        # l0 = sympy_to_z3(list(f0lb.free_symbols), f0lb)[1]
        # u0 = sympy_to_z3(list(f0ub.free_symbols), f0ub)[1]

        # f1 = sympy_to_z3(list(f1expr.free_symbols), f1expr)[1]
        # l1 = sympy_to_z3(list(f1lb.free_symbols), f1lb)[1]
        # u1 = sympy_to_z3(list(f1ub.free_symbols), f1ub)[1]

        # P0 = list(map(lambda x: sympy_to_z3(list(x.free_symbols), x)[1], p0.P))

        # print('lb0 =', l0)
        # print('lb1 =', l1)

        # assert(False)
        # s = Solver()
        # orc = z3.And(*P0)
        # impc = z3.Implies(orc, eq_constraint)

        # nimp = z3.Not(impc)
        # s.add(nimp)

        # result = s.check()
        # if result == sat:
            # m = s.model()
        # return not (result == sat)

    f0 = sympy_to_z3(list(p0.f.free_symbols), p0.f)[1]
    P0 = list(map(lambda x: sympy_to_z3(list(x.free_symbols), x)[1], p0.P))

    f1 = sympy_to_z3(list(p1.f.free_symbols), p1.f)[1]


    f0ef1 = Eq(p0.f, p1.f)
    eq_constraint = (sympy_to_z3(f0ef1.free_symbols, f0ef1))[1]

    s = Solver()
    orc = z3.And(*P0)
    impc = z3.Implies(orc, eq_constraint)

    nimp = z3.Not(impc)
    s.add(nimp)

    result = s.check()
    if result == sat:
        m = s.model()
    return not (result == sat)

def num_basic_set(p):
    return len(p.get_basic_sets())

def isl_str(p):
    if isinstance(p, Equality):
        return str(p.lhs) + ' = ' + str(p.rhs)
    return str(p)

def to_isl_set(p):
    cstr = ' and '.join(map(lambda x: isl_str(x), p))
    varstr = ', '.join(map(isl_str, (set.union(*map(free_variables, p)))))
    setfmt = '[{0}] : {1}'.format(varstr, cstr)
    setstr = '{' + setfmt + '}'
    # print('Converting to setstr:', setstr)
    return isl.Set(setstr)

def from_isl_set(res):
    if num_basic_set(res) == 1:
        # print('\t\tCAN MERGE!')
        bset = res.get_basic_sets()[0]
        sympy_constraints = set()
        for c in bset.get_constraints():
            # print('\t\t\t', c)
            assert(not c.is_div_constraint())

            cg = 0
            # print('id dict:', c.get_id_dict())
            iddict = c.get_id_dict()
            coeff_dict = c.get_coefficients_by_name()
            # print('coeff dict:', coeff_dict)
            for v in iddict:
                # print('v =', v)
                # print('v =', v, 'val =', iddict[v])
                if v.name in coeff_dict:
                    cg = cg + symbols(v.name)*int(str(coeff_dict[v.name]))

            # print('cg =', cg)
            cg = cg + int(str(c.get_constant_val()))

            if c.is_equality():
                sympy_constraints.add(Eq(cg, 0))
                # print('\t\t\t\t', 'eq')
            else:
                sympy_constraints.add(cg >= 0)
                # print('\t\t\t\t', 'geq')
        return list(sympy_constraints)
    else:
        print('Cannot turn', res, 'has more than 1 basic set')
        assert(False)

def function_applications(pi):
    pifuncs = set()
    for cs in pi:
        for a in cs.atoms(Function):
            pifuncs.add(a)
    return pifuncs

def try_to_coalesce(pi, pj):
    funcapps = function_applications(pi + pj)
    print('funcapps:', funcapps)
    func_map = {}
    pli = copy.deepcopy(pi)
    plj = copy.deepcopy(pj)
    i = 0
    for f in funcapps:
        var = symbols('func_rep_' + str(i))
        print('replacing {0} with {1}'.format(f, var))
        pli = list(map(lambda x: x.subs(f, var), pli))
        plj = list(map(lambda x: x.subs(f, var), plj))
        i += 1
        func_map[var] = f
    print('pli =', pli)
    print('plj =', plj)
    # assert(len(funcapps) == 0)

    pset = to_isl_set(pli)
    lset = to_isl_set(plj)
    res = pset.union(lset).coalesce()

    if num_basic_set(res) == 1:
        resset = from_isl_set(res)
        for var in func_map:
            resset = list(map(lambda x: x.subs(var, func_map[var]), resset))
        return resset
    return None
    
def try_to_find_a_piece_to_merge(pieces):
    merged_a_piece = False
    for pi in pieces:
        for pj in pieces:
            if pi != pj:
                if can_merge_into(pi, pj):
                    resset = try_to_coalesce(pi.P, pj.P)

                    # if num_basic_set(res) == 1:
                    if resset != None:
                        # resset = from_isl_set(res)
                        pieces.remove(pi)
                        pieces.remove(pj)

                        pieces.add(Piece(pj.f, resset))

                        merged_a_piece = True
                        break
        if merged_a_piece:
            break
    return merged_a_piece



def merge_pieces_pw(k):
    assert(isinstance(k, PiecewiseExpression))

    pieces = set(k.pieces)
    while try_to_find_a_piece_to_merge(pieces):
        print('Merged a piece, size =', len(pieces))
        None
    kexpr = PiecewiseExpression()
    for k in pieces:
        print(k)
        kexpr.add_piece(k.f, k.P)
    return kexpr

def merge_pieces(ip):
    return mutate_after(ip, lambda x: merge_pieces_pw(x) if isinstance(x, PiecewiseExpression) else x)
        
def symmat():
    return PiecewiseExpression()

