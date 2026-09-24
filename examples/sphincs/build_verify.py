"""Assemble the compact candidate's RV64IM verifier for differential testing.

This prototype is not submitted until its exact Lean certificate exists.
"""

from pathlib import Path

from examples.hypertree.build import Assembler
from examples.sphincs.reference import CHAINS, DIGEST, FTS_HEIGHT, FTS_TREES, HEIGHTS, SIG_BYTES

SIGNATURE = 0x20060
WITNESS = 0x20060 + 8 * ((SIG_BYTES + 7) // 8)
CACHE, SECRET_KEY, PUBLIC_KEY = 0x60, 0x20, 0x40
HASH, ANSWER = 0x40000, 0x42000
LAYER, TREE, POS, INDEX, LEAF, PTR = range(0x43000, 0x43030, 8)
T, LEVEL, CHAIN, STEP, SUM, BASE, BIT, MSG_INDEX = range(0x43040, 0x43080, 8)
NEXT_BASE, NODE, COUNT = 0x43080, 0x43088, 0x43090
DIGITS, ROOTS, ENDPOINTS, LEAVES, CURRENT, VALUE = (
    0x44000, 0x44100, 0x44300, 0x44800, 0x44a00, 0x44b00)


class Builder(Assembler):
    def __init__(self, parameter_address=WITNESS + 20):
        super().__init__()
        self.parameter_address = parameter_address

    def lw(self, rd, base, offset=0): self.i(3, 6, rd, base, offset)

    def sw(self, rs, base, offset=0):
        assert -2048 <= offset < 2048
        imm = offset & 4095
        self.emit(((imm >> 5) << 25) | (rs << 20) | (base << 15) |
                  (2 << 12) | ((imm & 31) << 7) | 0x23)

    def cp20(self, source, destination):
        for offset in (0, 4, 8, 12, 16):
            self.lw(13, source, offset)
            self.sw(13, destination, offset)

    def cp(self, source, destination, size):
        assert size % 4 == 0
        self.li(6, source)
        self.li(7, destination)
        if size % 8 == 4:
            full = size - 4
        else:
            full = size
        if full:
            self.li(10, full // 8)
            label = self.fresh('copy')
            self.label(label)
            self.ld(11, 6)
            self.store(11, 7)
            self.i(0x13, 0, 6, 6, 8)
            self.i(0x13, 0, 7, 7, 8)
            self.i(0x13, 0, 10, 10, -1)
            self.branch(10, 0, label, True)
        if size % 8 == 4:
            self.lw(11, 6)
            self.sw(11, 7)

    def cp20_fixed(self, source, destination):
        self.li(6, source)
        self.li(7, destination)
        self.cp20(6, 7)

    def cp20_from_ptr(self, variable, destination):
        self.load(6, variable)
        self.li(7, destination)
        self.cp20(6, 7)

    def cp20_to_ptr(self, source, variable):
        self.li(6, source)
        self.load(7, variable)
        self.cp20(6, 7)

    def advance(self, variable, delta):
        self.load(6, variable)
        self.i(0x13, 0, 6, 6, delta)
        self.save(6, variable)

    def set_header(self, tag, with_parameter=True):
        self.li(6, 1 + (tag << 8))
        self.load(7, LAYER)
        self.shift(7, 7, 16)
        self.add(6, 6, 7)
        self.li(7, HASH)
        self.sw(6, 7)
        self.load(6, POS)
        self.sw(6, 7, 4)
        self.load(6, TREE)
        self.store(6, 7, 8)
        self.load(6, INDEX)
        self.sw(6, 7, 16)
        if with_parameter:
            self.cp20_fixed(self.parameter_address, HASH + 20)

    def hash(self, tag, byte_count, with_parameter=True):
        self.set_header(tag, with_parameter)
        self.li(10, HASH)
        self.li(11, byte_count * 8)
        self.li(12, ANSWER)
        self.li(5, 1)
        self.emit(0x73)

    def reject_if_different(self, left, right):
        okay = self.fresh('same')
        self.branch(left, right, okay)
        self.jump('reject')
        self.label(okay)

    def reject_if_nonzero(self, reg): self.reject_if_different(reg, 0)

    def compare20(self, left, right):
        self.li(6, left)
        self.li(7, right)
        for offset in (0, 4, 8, 12, 16):
            self.lw(10, 6, offset)
            self.lw(11, 7, offset)
            self.reject_if_different(10, 11)

    def variable_header(self, layer, tree, position, index):
        self.set(LAYER, layer)
        self.set(TREE, tree)
        self.set(POS, position)
        self.set(INDEX, index)


def commitment(a):
    a.variable_header(0, 0, 0, 0)
    a.cp20_fixed(WITNESS, HASH + 20)
    a.cp20_fixed(WITNESS + 20, HASH + 40)
    a.hash(13, 60, with_parameter=False)
    a.li(6, ANSWER)
    a.li(7, 0x40)
    for offset in (0, 8):
        a.ld(10, 6, offset)
        a.ld(11, 7, offset)
        a.reject_if_different(10, 11)


def message_index(a):
    a.cp20_fixed(WITNESS + 40, HASH + 40)
    a.cp20_fixed(WITNESS, HASH + 60)
    a.cp(0, HASH + 80, 32)
    a.hash(12, 112)
    a.li(6, ANSWER)
    a.ld(10, 6)
    a.shift(10, 10, 30)
    a.shift(10, 10, 30, True)
    a.save(10, INDEX)
    a.save(10, MSG_INDEX)
    for tree in range(25):
        a.li(6, ANSWER)
        a.lbu(10, 6, 4 + tree)
        a.lbu(11, 6, 5 + tree)
        a.shift(10, 10, 2, True)
        a.shift(11, 11, 6)
        a.add(10, 10, 11)
        a.andi(10, 10, 255)
        if tree == 24:
            a.reject_if_nonzero(10)
        else:
            a.li(7, LEAVES + tree)
            a.store(10, 7, byte=True)


def fts(a):
    a.set(T, 0)
    a.set(PTR, WITNESS + 60)
    a.label('fts_tree')
    a.load(6, T)
    a.save(6, LAYER)
    a.load(6, MSG_INDEX)
    a.save(6, TREE)
    a.set(POS, 0)
    a.li(6, LEAVES)
    a.load(7, T)
    a.add(6, 6, 7)
    a.lbu(10, 6)
    a.save(10, LEAF)
    a.save(10, BIT)
    a.cp20_from_ptr(PTR, HASH + 40)
    a.advance(PTR, 20)
    a.load(6, LEAF)
    a.save(6, INDEX)
    a.hash(9, 60)
    a.cp20_fixed(ANSWER, CURRENT)
    a.set(LEVEL, 1)
    a.label('fts_level')
    a.load(6, BIT)
    a.andi(6, 6, 1)
    a.branch(6, 0, 'fts_left')
    a.cp20_from_ptr(PTR, HASH + 40)
    a.cp20_fixed(CURRENT, HASH + 60)
    a.jump('fts_pair_ready')
    a.label('fts_left')
    a.cp20_fixed(CURRENT, HASH + 40)
    a.cp20_from_ptr(PTR, HASH + 60)
    a.label('fts_pair_ready')
    a.advance(PTR, 20)
    a.load(6, BIT)
    a.shift(6, 6, 1, True)
    a.save(6, BIT)
    a.save(6, INDEX)
    a.load(6, LEVEL)
    a.save(6, POS)
    a.hash(10, 80)
    a.cp20_fixed(ANSWER, CURRENT)
    a.advance(LEVEL, 1)
    a.load(6, LEVEL)
    a.li(7, 9)
    a.branch(6, 7, 'fts_level', True)
    a.li(6, ROOTS)
    a.load(7, T)
    a.shift(10, 7, 2)
    a.shift(11, 7, 4)
    a.add(10, 10, 11)
    a.add(7, 6, 10)
    a.li(6, CURRENT)
    a.cp20(6, 7)
    a.advance(T, 1)
    a.load(6, T)
    a.li(7, FTS_TREES)
    a.branch(6, 7, 'fts_tree', True)
    a.variable_header(0, 0, 0, 0)
    a.load(6, MSG_INDEX)
    a.save(6, TREE)
    a.cp(ROOTS, HASH + 40, FTS_TREES * DIGEST)
    a.hash(11, 40 + FTS_TREES * DIGEST)
    a.cp20_fixed(ANSWER, CURRENT)


def layer(a, number, start):
    height = HEIGHTS[number]
    above = sum(HEIGHTS[:number])
    below = sum(HEIGHTS[number + 1:])
    a.set(LAYER, number)
    a.load(6, MSG_INDEX)
    a.shift(6, 6, 34 - above, True)
    a.save(6, TREE)
    a.load(6, MSG_INDEX)
    a.shift(6, 6, below, True)
    a.andi(6, 6, (1 << height) - 1)
    a.save(6, LEAF)
    a.set(POS, 0)
    a.load(6, LEAF)
    a.save(6, INDEX)
    a.cp20_fixed(CURRENT, HASH + 40)
    a.li(6, WITNESS + start)
    a.lw(10, 6)
    a.shift(11, 10, 20, True)
    a.reject_if_nonzero(11)
    a.li(7, HASH)
    a.sw(10, 7, 60)
    a.hash(4, 64)
    for offset in (9, 19):
        a.li(6, ANSWER)
        a.lbu(10, 6, offset)
        a.andi(10, 10, 0xC0)
        a.reject_if_nonzero(10)
    a.li(15, 0)
    for chain in range(CHAINS):
        bit = 3 * chain + (0 if chain < 26 else 2)
        offset, shift = divmod(bit, 8)
        a.li(6, ANSWER)
        a.lbu(10, 6, offset)
        if shift:
            a.shift(10, 10, shift, True)
        if shift > 5:
            a.lbu(11, 6, offset + 1)
            a.shift(11, 11, 8 - shift)
            a.add(10, 10, 11)
        a.andi(10, 10, 7)
        a.add(15, 15, 10)
        a.li(6, DIGITS + chain)
        a.store(10, 6, byte=True)
    a.li(10, 194)
    a.reject_if_different(15, 10)

    a.set(CHAIN, 0)
    a.set(PTR, WITNESS + start + 4)
    chain_loop = f'layer_{number}_chain'
    step_loop = f'layer_{number}_step'
    chain_end = f'layer_{number}_chain_end'
    a.label(chain_loop)
    a.cp20_from_ptr(PTR, VALUE)
    a.li(6, DIGITS)
    a.load(7, CHAIN)
    a.add(6, 6, 7)
    a.lbu(10, 6)
    a.save(10, STEP)
    a.label(step_loop)
    a.load(6, STEP)
    a.li(7, 7)
    a.branch(6, 7, chain_end)
    a.cp20_fixed(VALUE, HASH + 40)
    a.load(6, CHAIN)
    a.shift(6, 6, 3)
    a.load(7, STEP)
    a.add(6, 6, 7)
    a.save(6, POS)
    a.hash(1, 60)
    a.cp20_fixed(ANSWER, VALUE)
    a.advance(STEP, 1)
    a.jump(step_loop)
    a.label(chain_end)
    a.li(6, ENDPOINTS)
    a.load(7, CHAIN)
    a.shift(10, 7, 2)
    a.shift(11, 7, 4)
    a.add(10, 10, 11)
    a.add(7, 6, 10)
    a.li(6, VALUE)
    a.cp20(6, 7)
    a.advance(PTR, 20)
    a.advance(CHAIN, 1)
    a.load(6, CHAIN)
    a.li(7, CHAINS)
    a.branch(6, 7, chain_loop, True)
    a.set(POS, 0)
    a.cp(ENDPOINTS, HASH + 40, CHAINS * DIGEST)
    a.hash(2, 40 + CHAINS * DIGEST)
    a.cp20_fixed(ANSWER, CURRENT)

    a.load(6, LEAF)
    a.save(6, BIT)
    a.set(LEVEL, 1)
    node_loop = f'layer_{number}_node'
    left = f'layer_{number}_left'
    paired = f'layer_{number}_pair_ready'
    a.label(node_loop)
    a.load(6, BIT)
    a.andi(6, 6, 1)
    a.branch(6, 0, left)
    a.cp20_from_ptr(PTR, HASH + 40)
    a.cp20_fixed(CURRENT, HASH + 60)
    a.jump(paired)
    a.label(left)
    a.cp20_fixed(CURRENT, HASH + 40)
    a.cp20_from_ptr(PTR, HASH + 60)
    a.label(paired)
    a.advance(PTR, 20)
    a.load(6, BIT)
    a.shift(6, 6, 1, True)
    a.save(6, BIT)
    a.save(6, INDEX)
    a.load(6, LEVEL)
    a.save(6, POS)
    a.hash(3, 80)
    a.cp20_fixed(ANSWER, CURRENT)
    a.advance(LEVEL, 1)
    a.load(6, LEVEL)
    a.li(7, height + 1)
    a.branch(6, 7, node_loop, True)


def build():
    a = Builder()
    a.jump('start')
    a.label('reject')
    a.halt(False)
    a.label('start')
    commitment(a)
    message_index(a)
    fts(a)
    offsets = [60 + FTS_TREES * (1 + FTS_HEIGHT) * DIGEST]
    for height in HEIGHTS[:-1]:
        offsets.append(offsets[-1] + 4 + CHAINS * DIGEST + height * DIGEST)
    for number in reversed(range(len(HEIGHTS))):
        layer(a, number, offsets[number])
    a.compare20(CURRENT, WITNESS)
    a.halt(True)
    build.labels = a.labels
    return a.finish()


def build_expand():
    a = Builder()
    a.cp(SIGNATURE, WITNESS, SIG_BYTES)
    a.halt(True)
    return a.finish()


def build_keygen():
    a = Builder(CACHE + 20)
    a.variable_header(0, 0, 0, 0)
    a.cp(SECRET_KEY, HASH + 40, 32)
    a.hash(5, 72, with_parameter=False)
    a.cp20_fixed(ANSWER, CACHE + 20)
    a.set(LEAF, 0)
    a.label('keygen_leaf')
    a.set(CHAIN, 0)
    a.label('keygen_chain')
    a.load(6, CHAIN)
    a.save(6, POS)
    a.load(6, LEAF)
    a.save(6, INDEX)
    a.cp(SECRET_KEY, HASH + 40, 32)
    a.hash(0, 72)
    a.cp20_fixed(ANSWER, VALUE)
    a.set(STEP, 0)
    a.label('keygen_step')
    a.load(6, CHAIN)
    a.shift(6, 6, 3)
    a.load(7, STEP)
    a.add(6, 6, 7)
    a.save(6, POS)
    a.cp20_fixed(VALUE, HASH + 40)
    a.hash(1, 60)
    a.cp20_fixed(ANSWER, VALUE)
    a.advance(STEP, 1)
    a.load(6, STEP)
    a.li(7, 7)
    a.branch(6, 7, 'keygen_step', True)
    a.li(6, ENDPOINTS)
    a.load(7, CHAIN)
    a.shift(10, 7, 2)
    a.shift(11, 7, 4)
    a.add(10, 10, 11)
    a.add(7, 6, 10)
    a.li(6, VALUE)
    a.cp20(6, 7)
    a.advance(CHAIN, 1)
    a.load(6, CHAIN)
    a.li(7, CHAINS)
    a.branch(6, 7, 'keygen_chain', True)
    a.set(POS, 0)
    a.cp(ENDPOINTS, HASH + 40, CHAINS * DIGEST)
    a.hash(2, 40 + CHAINS * DIGEST)
    a.li(6, CACHE + 40)
    a.load(7, LEAF)
    a.shift(10, 7, 2)
    a.shift(11, 7, 4)
    a.add(10, 10, 11)
    a.add(7, 6, 10)
    a.li(6, ANSWER)
    a.cp20(6, 7)
    a.advance(LEAF, 1)
    a.load(6, LEAF)
    a.li(7, 1 << HEIGHTS[0])
    a.branch(6, 7, 'keygen_leaf', True)

    a.set(LEVEL, 1)
    a.set(BASE, CACHE + 40)
    a.set(NEXT_BASE, CACHE + 40 + (1 << HEIGHTS[0]) * DIGEST)
    a.set(COUNT, (1 << HEIGHTS[0]) // 2)
    a.label('keygen_level')
    a.set(NODE, 0)
    a.label('keygen_node')
    a.load(6, NODE)
    a.shift(10, 6, 3)
    a.shift(11, 6, 5)
    a.add(10, 10, 11)
    a.load(6, BASE)
    a.add(6, 6, 10)
    a.li(7, HASH + 40)
    a.cp20(6, 7)
    a.i(0x13, 0, 6, 6, 20)
    a.li(7, HASH + 60)
    a.cp20(6, 7)
    a.load(6, LEVEL)
    a.save(6, POS)
    a.load(6, NODE)
    a.save(6, INDEX)
    a.hash(3, 80)
    a.load(7, NODE)
    a.shift(10, 7, 2)
    a.shift(11, 7, 4)
    a.add(10, 10, 11)
    a.load(7, NEXT_BASE)
    a.add(7, 7, 10)
    a.li(6, ANSWER)
    a.cp20(6, 7)
    a.advance(NODE, 1)
    a.load(6, NODE)
    a.load(7, COUNT)
    a.branch(6, 7, 'keygen_node', True)
    a.load(6, NEXT_BASE)
    a.save(6, BASE)
    a.load(7, COUNT)
    a.shift(10, 7, 2)
    a.shift(11, 7, 4)
    a.add(10, 10, 11)
    a.add(6, 6, 10)
    a.save(6, NEXT_BASE)
    a.load(6, COUNT)
    a.shift(6, 6, 1, True)
    a.save(6, COUNT)
    a.advance(LEVEL, 1)
    a.load(6, LEVEL)
    a.li(7, HEIGHTS[0] + 1)
    a.branch(6, 7, 'keygen_level', True)
    a.load(6, BASE)
    a.li(7, CACHE)
    a.cp20(6, 7)
    a.variable_header(0, 0, 0, 0)
    a.cp20_fixed(CACHE, HASH + 20)
    a.cp20_fixed(CACHE + 20, HASH + 40)
    a.hash(13, 60, with_parameter=False)
    a.cp(ANSWER, PUBLIC_KEY, 16)
    a.halt(True)
    return a.finish()


if __name__ == '__main__':
    images = {'keygen': build_keygen(), 'expand': build_expand(), 'verify': build()}
    target = Path(__file__).resolve().parents[2] / 'SigGolfCandidate/SphincsImages.lean'
    lines = [
        '-- Generated by examples/sphincs/build_verify.py. A full certificate is still required.',
        'import SigGolf',
        '',
        'namespace SigGolfCandidate.SphincsImages',
        'open SigGolf',
        'set_option maxRecDepth 16384',
        '',
    ]
    for phase, words in images.items():
        lines += [f'def {phase} : Riscv.Image where', '  code := [']
        lines += ['    ' + ', '.join(f'0x{word:08x}' for word in words[i:i + 8]) +
                  (',' if i + 8 < len(words) else ']')
                  for i in range(0, len(words), 8)]
        lines += ['  data := []', '']
    lines += ['end SigGolfCandidate.SphincsImages', '']
    target.write_text('\n'.join(lines))
    for phase, words in images.items():
        print(phase + ':', len(words), 'instructions,', 4 * len(words), 'image bytes')
