class AffineExpr:

    def __init__(self, coeffs, offset):
        self.coeffs = coeffs
        self.offset = offset

    def __repr__(self):
        ss = ''
        for c in self.coeffs:
            ss += str(self.coeffs[c]) + ' ' + c + ' + ';
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
        val = 0
        for v in self.coeffs:
            print(v)
            val += coeff_vals[v]*self.coeffs[v]
        val += self.offset
        if self.comparator == '=':
            return val == 0
        else:
            assert(False)
            return -1

class Piece:

    def __init__(self, value, constraints):
        self.value = value
        self.constraints = constraints

    def contains(self, r, c):
        for cs in self.constraints:
            if cs.evaluate({'r' : r, 'c' : c}) == False:
                return False
        return True

    def at(self, r, c):
        return self.value

class Matrix:

    def __init__(self, name, rows, cols):
        self.rows = rows
        self.cols = cols
        self.name = name
        self.pieces = []
        self.pieces.append(Piece(0, []))

    def add_piece(self, value, constraints):
        self.pieces[value] = constraints

    def realize(self, values):
        None

    def at(self, r, c):
        for piece in self.pieces:
            if piece.contains(r, c):
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

# Building a zero matrix
D = Matrix('D', 'm', 'n')
print(D)

D.realize({'m' : 10, 'n' : 10})

assert(D.at(0, 0) == 0)

D = Matrix('D', 'm', 'n')
D.paste_region(1, [Constraint({'r' : 1, 'c' : -1}, 0, '=')])
print(D)

D.realize({'m' : 10, 'n' : 10})

assert(D.at(0, 0) == 1)
assert(D.at(1, 0) == 0)

A = D.cylindrical_decomposition()

assert(len(A.pieces) == 3)



