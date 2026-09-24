"""Differentially test the full signing image and its cache checks."""

from examples.sphincs.build_images import CACHE, SECRET_KEY, SIGNATURE
from examples.sphincs.check_verify import Machine
from examples.sphincs.reference import (
    CACHE_BYTES, Oracle, SIG_BYTES, keygen, layer_address, message_index,
    parse_signature, sign, verify,
)
from examples.sphincs.sign_image import build_sign


def run(code: list[int], seed: bytes, message: bytes, pk: bytes, cache: bytes) -> Machine:
    machine = Machine(code, message, pk, bytes(SIG_BYTES))
    machine.mem[SECRET_KEY:SECRET_KEY + 32] = seed
    machine.mem[CACHE:CACHE + CACHE_BYTES] = cache
    machine.run(100_000_000)
    return machine


def main() -> None:
    seed = bytes(range(32))
    message = bytes(reversed(range(32)))
    oracle = Oracle()
    pk, cache = keygen(oracle, seed)
    expected = sign(oracle, seed, pk, cache, message)
    code = build_sign()
    machine = run(code, seed, message, pk, cache)
    signature = bytes(machine.mem[SIGNATURE:SIGNATURE + SIG_BYTES])
    assert machine.accepted and signature == expected
    assert verify(Oracle(), pk, message, signature)
    assert machine.oracle.compressions < 1 << 17
    print("sign:", machine.instructions, "instructions,", machine.cycles,
          "cycles,", machine.oracle.compressions, "compressions")

    changed = bytearray(cache)
    changed[20] ^= 1  # A different public parameter must fail before signing.
    assert not run(code, seed, message, pk, bytes(changed)).accepted

    parsed = parse_signature(expected)
    assert parsed is not None
    index, _ = message_index(Oracle(), parsed.parameter, parsed.root, message, parsed.rho)
    top_leaf = layer_address(index, 0)[1]
    changed = bytearray(cache)
    changed[40 + 20 * (top_leaf ^ 1)] ^= 1  # Corrupt the selected top authentication path.
    assert not run(code, seed, message, pk, bytes(changed)).accepted


if __name__ == "__main__":
    main()
