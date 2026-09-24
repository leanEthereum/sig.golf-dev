"""Costly, full-image keygen comparison; run only after changing keygen code."""

from examples.sphincs.build_images import CACHE, PUBLIC_KEY, SECRET_KEY, build_keygen
from examples.sphincs.check_verify import Machine
from examples.sphincs.reference import CACHE_BYTES, Oracle, SIG_BYTES, keygen


def main() -> None:
    seed = bytes(range(32))
    oracle = Oracle()
    expected_pk, expected_cache = keygen(oracle, seed)
    machine = Machine(build_keygen(), bytes(32), bytes(16), bytes(SIG_BYTES))
    machine.mem[SECRET_KEY:SECRET_KEY + 32] = seed
    machine.run(200_000_000)
    assert machine.accepted
    assert machine.mem[PUBLIC_KEY:PUBLIC_KEY + 16] == expected_pk
    assert machine.mem[CACHE:CACHE + CACHE_BYTES] == expected_cache
    assert machine.oracle.compressions == 997377
    print("keygen:", machine.instructions, "instructions,", machine.cycles,
          "cycles,", machine.oracle.compressions, "compressions")


if __name__ == "__main__":
    main()
