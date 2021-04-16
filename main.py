class Constraint:

    def __init__(self, rc, cc, bc, b, comparator):
        self.rc = rc
        self.cc = cc
        self.bc = bc
        self.b = b
        self.comparator = comparator

class Piece:

    def __init__(self, value, constraints):
        self.value = value
        self.constraints = constraints

    def contains(self, r, c):
        return True

    def at(self, r, c):
        return self.value

class Matrix:

    def __init__(self, name, rows, cols):
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

    def __repr__(self):
        return self.name

# Building a zero matrix
D = Matrix('D', 'm', 'n')
print(D)

D.realize({'m' : 10, 'n' : 10})

assert(D.at(0, 0) == 0)

# cc = Constraint(1, 1, 0, 0, '=')
# A.add_piece('a', [cc])

D = Matrix('D', 'm', 'n')
D.paste_region(1, [Constraint([1, -1], 0, '=')])
print(D)

D.realize({'m' : 10, 'n' : 10})

assert(D.at(0, 0) == 1)
