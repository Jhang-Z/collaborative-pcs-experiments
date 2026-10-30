"""Fixed Boolean Keccak DAG and odd-characteristic R1CS for Pappas.

Signals -1/-2 are zero/one; input signals 0..1599 are private state bits.
R1CS wire0 is public constant one; other wires are signals shifted by one.
"""
from dataclasses import dataclass
import struct

PRIME = (1 << 61) - 1
ZERO, ONE = -1, -2
RC = (
    0x0000000000000001,0x0000000000008082,0x800000000000808a,0x8000000080008000,
    0x000000000000808b,0x0000000080000001,0x8000000080008081,0x8000000000008009,
    0x000000000000008a,0x0000000000000088,0x0000000080008009,0x000000008000000a,
    0x000000008000808b,0x800000000000008b,0x8000000000008089,0x8000000000008003,
    0x8000000000008002,0x8000000000000080,0x000000000000800a,0x800000008000000a,
    0x8000000080008081,0x8000000000008080,0x0000000080000001,0x8000000080008008)
ROT = (0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14)

@dataclass
class Circuit:
    gates: list
    outputs: tuple

    @classmethod
    def build(cls):
        gates = []
        def value(a):
            return a == ONE
        def gate(op, a, b=ZERO):
            if op == 'not':
                if a < 0:
                    return ZERO if value(a) else ONE
            elif a < 0 and b < 0:
                x, y = value(a), value(b)
                return ONE if (x & y if op == 'and' else x ^ y) else ZERO
            elif op == 'and':
                if a == ZERO or b == ZERO: return ZERO
                if a == ONE: return b
                if b == ONE or a == b: return a
            else:
                if a == ZERO: return b
                if b == ZERO: return a
                if a == b: return ZERO
                if a == ONE: return gate('not', b)
                if b == ONE: return gate('not', a)
            out = 1600 + len(gates)
            gates.append((op, a, b))
            return out
        def xor_words(a, b):
            return tuple(gate('xor', x, y) for x, y in zip(a, b))
        def rotate(word, n):
            return tuple(word[(i-n)%64] for i in range(64))
        state = [tuple(range(64*i, 64*i+64)) for i in range(25)]
        for constant in RC:
            columns = []
            for x in range(5):
                c = state[x]
                for y in range(1, 5): c = xor_words(c, state[x+5*y])
                columns.append(c)
            delta = [xor_words(columns[(x-1)%5], rotate(columns[(x+1)%5], 1)) for x in range(5)]
            moved = [None]*25
            for y in range(5):
                for x in range(5):
                    moved[y+5*((2*x+3*y)%5)] = rotate(xor_words(state[x+5*y], delta[x]), ROT[x+5*y])
            state = []
            for y in range(5):
                for x in range(5):
                    state.append(tuple(gate('xor', moved[x+5*y][bit],
                        gate('and', gate('not', moved[(x+1)%5+5*y][bit]),
                             moved[(x+2)%5+5*y][bit])) for bit in range(64)))
            state[0] = tuple(gate('not', signal) if constant >> bit & 1 else signal
                             for bit, signal in enumerate(state[0]))
        return cls(gates, tuple(signal for word in state[:4] for signal in word))

    @property
    def public_start(self):
        return 1 + 1600 + len(self.gates)

    @property
    def row_count(self):
        return 1600 + len(self.gates) + 256

    def witness(self, data):
        if len(data) != 200:
            raise ValueError('Keccak requires one 200-byte state')
        values = [(data[i//8] >> (i%8)) & 1 for i in range(1600)]
        def v(signal):
            return int(signal == ONE) if signal < 0 else values[signal]
        for op, a, b in self.gates:
            x, y = v(a), v(b)
            values.append(1-x if op == 'not' else x*y if op == 'and' else x^y)
        public = [v(s) for s in self.outputs]
        output = bytes(sum(public[8*i+j] << j for j in range(8)) for i in range(32))
        return [1] + values + public, output

    def rows(self):
        def term(signal, coefficient=1):
            if signal == ZERO: return []
            return [(0 if signal == ONE else signal+1, coefficient)]
        for i in range(1, 1601):
            yield [(i,1)], [(i,1),(0,-1)], []
        for i, (op, a, b) in enumerate(self.gates):
            out = 1601+i
            if op == 'and':
                yield term(a), term(b), [(out,1)]
            elif op == 'xor':
                yield term(a,2), term(b), term(a)+term(b)+[(out,-1)]
            else:
                yield [(0,1)]+term(a,-1), [(0,1)], [(out,1)]
        for i, signal in enumerate(self.outputs):
            yield term(signal)+[(self.public_start+i,-1)], [(0,1)], []

    def check(self, witness, output):
        if len(witness) != self.public_start+256 or len(output) != 32 or witness[0] != 1:
            return False
        if witness[self.public_start:] != [(output[i//8] >> (i%8)) & 1 for i in range(256)]:
            return False
        for a, b, c in self.rows():
            dot = lambda row: sum(witness[i]*v for i,v in row) % PRIME
            if (dot(a)*dot(b)-dot(c)) % PRIME:
                return False
        return True

    def encode(self):
        out = bytearray(b'PKECR001'+struct.pack('<QQQ',self.row_count,self.public_start+256,self.public_start))
        for row in self.rows():
            for lc in row:
                out.extend(struct.pack('<Q',len(lc)))
                for wire, coefficient in lc:
                    out.extend(struct.pack('<Qq',wire,coefficient))
        return out
