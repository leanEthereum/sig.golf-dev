"""Differentially test the assembled RV64IM verifier against the Python oracle model."""

from __future__ import annotations

import hashlib

from examples.sphincs.build_verify import SIGNATURE, WITNESS, build, build_expand
from examples.sphincs.reference import (
    Oracle, keygen, layer_address, message_index, parse_signature, sign, verify,
    SIG_BYTES, VERIFY_COMPRESSIONS,
)

MASK = (1 << 64) - 1


def signed(value: int, bits: int) -> int:
    return value - (1 << bits) if value & (1 << (bits - 1)) else value


class Machine:
    def __init__(self, code: list[int], message: bytes, pk: bytes, witness: bytes):
        self.code = code
        self.mem = bytearray(1 << 24)
        self.mem[0:32] = message
        self.mem[0x40:0x50] = pk
        self.mem[WITNESS:WITNESS + SIG_BYTES] = witness
        self.regs = [0] * 32
        self.regs[2] = len(self.mem)
        self.pc = 0x1000
        self.cycles = 0
        self.instructions = 0
        self.oracle = Oracle()
        self.accepted = None

    def access(self, address: int, width: int) -> None:
        assert address % width == 0 and address + width <= len(self.mem), (
            "bad memory access", hex(self.pc), hex(address), width)

    def run(self, limit: int = 2_000_000) -> None:
        r, mem, code = self.regs, self.mem, self.code
        for _ in range(limit):
            assert self.pc >= 0x1000 and self.pc % 4 == 0
            position = (self.pc - 0x1000) // 4
            assert position < len(code), ("bad fetch", hex(self.pc))
            word = code[position]
            opcode, rd, funct3 = word & 127, (word >> 7) & 31, (word >> 12) & 7
            rs1, rs2 = (word >> 15) & 31, (word >> 20) & 31
            immediate = signed(word >> 20, 12)
            next_pc = self.pc + 4
            cost = 1
            if opcode == 0x37:
                r[rd] = signed(word & 0xFFFFF000, 32) & MASK
            elif opcode == 0x13:
                if funct3 == 0: r[rd] = (r[rs1] + immediate) & MASK
                elif funct3 == 1: r[rd] = (r[rs1] << ((word >> 20) & 63)) & MASK
                elif funct3 == 5:
                    assert word >> 26 == 0
                    r[rd] >>= (word >> 20) & 63
                elif funct3 == 7: r[rd] &= immediate & MASK
                else: raise AssertionError(("op-imm", hex(word), hex(self.pc)))
            elif opcode == 0x33:
                assert funct3 == 0 and word >> 25 == 0
                r[rd] = (r[rs1] + r[rs2]) & MASK
            elif opcode == 3:
                width = {3: 8, 6: 4, 4: 1}[funct3]
                address = (r[rs1] + immediate) & MASK
                self.access(address, width)
                r[rd] = int.from_bytes(mem[address:address + width], "little")
            elif opcode == 0x23:
                immediate = signed(((word >> 25) << 5) | ((word >> 7) & 31), 12)
                width = {3: 8, 2: 4, 0: 1}[funct3]
                address = (r[rs1] + immediate) & MASK
                self.access(address, width)
                mem[address:address + width] = (r[rs2] & ((1 << (8 * width)) - 1)).to_bytes(width, "little")
            elif opcode == 0x63:
                immediate = signed(((word >> 31) << 12) | (((word >> 7) & 1) << 11) |
                                   (((word >> 25) & 63) << 5) | (((word >> 8) & 15) << 1), 13)
                assert funct3 in (0, 1)
                if (r[rs1] == r[rs2]) != bool(funct3):
                    next_pc = self.pc + immediate
            elif opcode == 0x6F:
                immediate = signed(((word >> 31) << 20) | (((word >> 12) & 255) << 12) |
                                   (((word >> 20) & 1) << 11) | (((word >> 21) & 1023) << 1), 21)
                r[rd], next_pc = next_pc, self.pc + immediate
            elif opcode == 0x67:
                assert funct3 == 0
                r[rd], next_pc = next_pc, (r[rs1] + immediate) & MASK & ~1
            elif word == 0x73:
                if r[5] == 0:
                    self.accepted = r[10] == 1
                    self.cycles += 1
                    self.instructions += 1
                    return
                assert r[5] == 1
                source, bits, target = r[10], r[11], r[12]
                assert source % 8 == target % 8 == bits % 8 == 0
                self.access(source, 8)
                self.access(target, 8)
                self.access(source + (bits + 7) // 8 - 1, 1)
                self.access(target + 31, 1)
                payload = bytes(mem[source:source + bits // 8])
                answer = self.oracle(payload)
                mem[target:target + 32] = answer
                cost = 8 * max(1, (len(payload) + 63) // 64)
            else:
                raise AssertionError(("unknown instruction", hex(word), hex(self.pc)))
            r[0] = 0
            self.pc = next_pc & MASK
            self.cycles += cost
            self.instructions += 1
        raise AssertionError("verification did not finish")


def main() -> None:
    seed = bytes(range(32))
    oracle = Oracle()
    pk, cache = keygen(oracle, seed)
    code = build()
    print("image", len(code), "instructions", 4 * len(code), "bytes")
    for number in range(3):
        message = hashlib.sha256(f"sample-{number}".encode()).digest()
        witness = sign(oracle, seed, pk, cache, message)
        assert verify(oracle, pk, message, witness)
        machine = Machine(code, message, pk, witness)
        machine.run()
        assert machine.accepted
        assert machine.oracle.compressions == VERIFY_COMPRESSIONS
        parsed = parse_signature(witness)
        assert parsed is not None
        index, leaves = message_index(oracle, parsed.parameter, parsed.root, message, parsed.rho)
        popcount = lambda value: bin(value).count("1")
        rights = sum(map(popcount, leaves[:24])) + sum(
            popcount(layer_address(index, layer)[1]) for layer in range(6))
        assert machine.instructions == 159530 + rights
        assert machine.cycles == 171173 + rights <= 171399
        print("sample", number, machine.instructions, "instructions", machine.cycles, "cycles")
        expanded = Machine(build_expand(), message, pk, bytes(SIG_BYTES))
        expanded.mem[SIGNATURE:SIGNATURE + SIG_BYTES] = witness
        expanded.run()
        assert expanded.accepted and expanded.mem[WITNESS:WITNESS + SIG_BYTES] == witness
        changed = bytearray(witness)
        changed[4382] |= 0x10
        broken = Machine(code, message, pk, bytes(changed))
        broken.run()
        assert not broken.accepted


if __name__ == "__main__":
    main()
