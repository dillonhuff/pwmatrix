import copy

class Var:

    def __init__(self, name):
        self.name = name

    def __hash__(self):
        return hash(self.name)

    def __eq__(self, other):
        return isinstance(other, Var) and other.name == self.name
    
    def __repr__(self):
        return self.name

class AffineExpr:

    def __init__(self, coeffs, offset):
        self.coeffs = coeffs
        self.offset = offset

    def evaluate(self, coeff_vals):
        val = 0
        for v in self.coeffs:
            print(v)
            val += (coeff_vals[v] if v in coeff_vals else 0)*self.coeffs[v]
        val += self.offset
        print('Evaluation of {0} at {1} = {2}'.format(self, coeff_vals, val))
        return val

    def __repr__(self):
        ss = ''
        for c in self.coeffs:
            ss += str(self.coeffs[c]) + ' ' + str(c) + ' + ';
        ss += str(self.offset)
        return ss

class Constraint:

    def __init__(self, coeffs, offset, comparator):
        self.coeffs = coeffs
        self.offset = offset
        self.comparator = comparator

    def __repr__(self):
        return '{0} {1} 0'.format(AffineExpr(self.coeffs, self.offset), self.comparator)

    def evaluate(self, coeff_vals):
        val =  AffineExpr(self.coeffs, self.offset).evaluate(coeff_vals)
        if self.comparator == '=':
            return val == 0
        elif self.comparator == '>=':
            return val >= 0
        elif self.comparator == '<=':
            return val <= 0
        else:
            assert(False)
            return -1

def substitute(target, replacement, c):
    print('substituting {0} for {1} in {2}'.format(replacement, target, c))
    if target in c.coeffs:
        value = c.coeffs[target]
        rep = replacement*value
        c.coeffs.pop(target)
        c.offset += rep
    print('Result: {0}'.format(c))
    return c

class Piece:

    def __init__(self, value, constraints):
        self.value = value
        self.constraints = constraints

    def contains(self, r, c):
        print('Checking containment', r, c)
        for cs in self.constraints:
            if cs.evaluate({Var('r') : r, Var('c') : c}) == False:
                print('{0}, {1} does not satisfy {2}'.format(r, c, cs))
                return False
            else:
                print('{0}, {1} satisfies {2}'.format(r, c, cs))
        return True

    def at(self, r, c):
        return self.value

    def __repr__(self):
        return '{0} at {1}'.format(self.value, self.constraints)

class Matrix:

    def __init__(self, name, rows, cols):
        self.rows = rows
        self.cols = cols

        self.name = name

        # TODO: Change to extract free variables from expressions
        self.parameters = [rows, cols]

        self.pieces = []

        r = Var('r')
        c = Var('c')

        cs = []
        cs.append(Constraint({r : 1}, 1, '>='))
        cs.append(Constraint({r : -1, rows : 1}, 0, '>='))
        cs.append(Constraint({c : 1}, 1, '>='))
        cs.append(Constraint({c : -1, cols : 1}, 0, '>='))
        self.pieces.append(Piece(0, cs))

    def add_piece(self, value, constraints):
        self.pieces[value] = constraints

    def realize(self, values):
        new_pieces = []
        for piece in self.pieces:
            realized = copy.deepcopy(piece)
            for c in realized.constraints:
                for v in values:
                    substitute(v, values[v], c)
            new_pieces.append(realized)
        self.pieces = new_pieces

        print('Parameters:', self.parameters)
        for v in values:
            print('removing: {0}'.format(v))
            self.parameters.remove(v)

    def at(self, r, c):
        for piece in self.pieces:
            if piece.contains(r, c):
                print(piece, 'contains', r, c)
                return piece.at(r, c)
        assert(False)

    def cylindrical_decomposition(self):
        A = Matrix(self.name, self.rows, self.cols)
        # This function should modify the matrix
        # so that the piecewise function it represents
        # returns whatever the value was before this
        # operation if the value is outside this piece,
        # and whatever the value is inside this piece
        # otherwise

        decomposed_pieces = []
        all_constraints = []
        for p in self.pieces:
            for cs in p.constraints:
                all_constraints.append(cs)
        for c in all_constraints:
            print(c)
        A.pieces = decomposed_pieces
        assert(False)
        return A

    def paste_region(self, value, constraints):
        self.pieces.insert(0, Piece(value, constraints))

    def __repr__(self):
        return self.name

m = Var('m')
n = Var('n')
r = Var('r')
c = Var('c')

# Building a zero matrix
D = Matrix('D', m, n)
print(D)

D.realize({m : 10, n : 10})

assert(D.at(1, 1) == 0)

D = Matrix('D', m, n)
D.paste_region(1, [Constraint({r : 1, c : -1}, 0, '=')])
print(D)

D.realize({m : 10, n : 10})

for p in D.pieces:
    print(p)

assert(D.at(1, 1) == 1)
assert(D.at(1, 2) == 0)

A = D.cylindrical_decomposition()

assert(len(A.pieces) == 3)



