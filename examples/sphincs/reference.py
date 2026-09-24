"""Executable test oracle for the compact SPHINCS candidate; not its Lean certificate.

The byte format matches SigGolfCandidate/SphincsWire.lean. SHA-256 is used only
to supply deterministic answers to the competition's abstract random oracle.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass

DIGEST = 20
CHAINS = 52
HEIGHTS = (11, 5, 5, 5, 4, 4)
FTS_TREES = 24
FTS_HEIGHT = 8
SIG_BYTES = 11324
CACHE_BYTES = 1 << 17
VERIFY_COMPRESSIONS = (1 + 2 + FTS_TREES * (1 + 2 * FTS_HEIGHT) + 9
                       + len(HEIGHTS) * (1 + 17 + 170) + 2 * sum(HEIGHTS))


class Oracle:
    def __init__(self) -> None:
        self.calls = 0
        self.compressions = 0

    def __call__(self, data: bytes) -> bytes:
        self.calls += 1
        self.compressions += max(1, (len(data) + 63) // 64)
        return hashlib.sha256(data).digest()


def word(value: int, size: int) -> bytes:
    return value.to_bytes(size, "little")


def tweak(tag: int, layer: int = 0, tree: int = 0,
          position: int = 0, index: int = 0) -> bytes:
    assert 0 <= tag < 256 and 0 <= layer < 256
    return bytes((1, tag, layer, 0)) + word(position, 4) + word(tree, 8) + word(index, 4)


def h(oracle: Oracle, parameter: bytes, tag: int, payload: bytes,
      layer: int = 0, tree: int = 0, position: int = 0,
      index: int = 0) -> bytes:
    assert len(parameter) == DIGEST
    return oracle(tweak(tag, layer, tree, position, index) + parameter + payload)[:DIGEST]


def parameter_from_seed(oracle: Oracle, seed: bytes) -> bytes:
    return h(oracle, bytes(DIGEST), 5, seed)


def ots_secret(oracle: Oracle, seed: bytes, p: bytes,
               layer: int, tree: int, leaf: int, chain: int) -> bytes:
    return h(oracle, p, 0, seed, layer, tree, chain, leaf)


def chain_step(oracle: Oracle, p: bytes, value: bytes,
               layer: int, tree: int, leaf: int, chain: int, step: int) -> bytes:
    return h(oracle, p, 1, value, layer, tree, 8 * chain + step, leaf)


def chain_walk(oracle: Oracle, p: bytes, value: bytes,
               layer: int, tree: int, leaf: int, chain: int,
               start: int, stop: int) -> bytes:
    for step in range(start, stop):
        value = chain_step(oracle, p, value, layer, tree, leaf, chain, step)
    return value


def ots_leaf(oracle: Oracle, seed: bytes, p: bytes,
             layer: int, tree: int, leaf: int) -> bytes:
    endpoints = []
    for chain in range(CHAINS):
        secret = ots_secret(oracle, seed, p, layer, tree, leaf, chain)
        endpoints.append(chain_walk(oracle, p, secret, layer, tree, leaf, chain, 0, 7))
    return h(oracle, p, 2, b"".join(endpoints), layer, tree, 0, leaf)


def node_hash(oracle: Oracle, p: bytes, left: bytes, right: bytes,
              layer: int, tree: int, level: int, index: int) -> bytes:
    return h(oracle, p, 3, left + right, layer, tree, level, index)


def ots_tree(oracle: Oracle, seed: bytes, p: bytes,
             layer: int, tree: int) -> list[list[bytes]]:
    levels = [[ots_leaf(oracle, seed, p, layer, tree, leaf)
               for leaf in range(1 << HEIGHTS[layer])]]
    for level in range(1, HEIGHTS[layer] + 1):
        previous = levels[-1]
        levels.append([node_hash(oracle, p, previous[2 * i], previous[2 * i + 1],
                                 layer, tree, level, i)
                       for i in range(len(previous) // 2)])
    return levels


def path(levels: list[list[bytes]], leaf: int) -> list[bytes]:
    return [nodes[(leaf >> level) ^ 1] for level, nodes in enumerate(levels[:-1])]


def cache_encode(p: bytes, levels: list[list[bytes]]) -> bytes:
    root = levels[-1][0]
    value = root + p + b"".join(node for level in levels for node in level)
    assert len(value) == 40 + 4095 * DIGEST
    return value.ljust(CACHE_BYTES, b"\0")


def cache_path(cache: bytes, leaf: int) -> list[bytes]:
    offset = 40
    result = []
    for level in range(HEIGHTS[0]):
        index = (leaf >> level) ^ 1
        result.append(cache[offset + DIGEST * index:offset + DIGEST * (index + 1)])
        offset += DIGEST * (1 << (HEIGHTS[0] - level))
    return result


def public_key(oracle: Oracle, root: bytes, p: bytes) -> bytes:
    return oracle(tweak(13) + root + p)[:16]


def keygen(oracle: Oracle, seed: bytes) -> tuple[bytes, bytes]:
    assert len(seed) == 32
    p = parameter_from_seed(oracle, seed)
    levels = ots_tree(oracle, seed, p, 0, 0)
    root = levels[-1][0]
    return public_key(oracle, root, p), cache_encode(p, levels)


def digest_encoding(oracle: Oracle, p: bytes, message: bytes,
                    counter: int, layer: int, tree: int, leaf: int) -> list[int] | None:
    digest = h(oracle, p, 4, message + word(counter, 4), layer, tree, 0, leaf)
    value = int.from_bytes(digest, "little")
    if value & (3 << 78 | 3 << 158):
        return None
    digits = [value >> (3 * i + (0 if i < 26 else 2)) & 7 for i in range(CHAINS)]
    return digits if sum(digits) == 194 else None


def ots_sign(oracle: Oracle, seed: bytes, p: bytes, message: bytes,
             layer: int, tree: int, leaf: int) -> tuple[int, list[bytes]]:
    for counter in range(1 << 20):
        digits = digest_encoding(oracle, p, message, counter, layer, tree, leaf)
        if digits is not None:
            values = []
            for chain, digit in enumerate(digits):
                secret = ots_secret(oracle, seed, p, layer, tree, leaf, chain)
                values.append(chain_walk(oracle, p, secret, layer, tree, leaf,
                                         chain, 0, digit))
            return counter, values
    raise ValueError("encoding attempts exhausted")


def fts_secret(oracle: Oracle, seed: bytes, p: bytes,
               index: int, tree: int, leaf: int) -> bytes:
    return h(oracle, p, 8, seed, tree, index, 0, leaf)


def fts_tree(oracle: Oracle, seed: bytes, p: bytes,
             index: int, tree: int) -> list[list[bytes]]:
    levels = [[h(oracle, p, 9, fts_secret(oracle, seed, p, index, tree, leaf),
                 tree, index, 0, leaf) for leaf in range(1 << FTS_HEIGHT)]]
    for level in range(1, FTS_HEIGHT + 1):
        previous = levels[-1]
        levels.append([h(oracle, p, 10, previous[2 * i] + previous[2 * i + 1],
                         tree, index, level, i)
                       for i in range(len(previous) // 2)])
    return levels


def fts_root(oracle: Oracle, p: bytes, index: int, roots: list[bytes]) -> bytes:
    assert len(roots) == FTS_TREES
    return h(oracle, p, 11, b"".join(roots), 0, index)


def message_index(oracle: Oracle, p: bytes, root: bytes,
                  message: bytes, rho: bytes) -> tuple[int, list[int]]:
    output = oracle(tweak(12) + p + rho + root + message)
    value = int.from_bytes(output, "little")
    value &= (1 << 234) - 1
    index = value & ((1 << 34) - 1)
    leaves = [(value >> (34 + 8 * tree)) & 255 for tree in range(25)]
    return index, leaves


def layer_address(index: int, layer: int) -> tuple[int, int]:
    above = sum(HEIGHTS[:layer])
    below = 34 - above - HEIGHTS[layer]
    return index >> (34 - above), (index >> below) & ((1 << HEIGHTS[layer]) - 1)


@dataclass
class Signature:
    root: bytes
    parameter: bytes
    rho: bytes
    fts: list[tuple[bytes, list[bytes]]]
    layers: list[tuple[int, list[bytes], list[bytes]]]

    def encode(self) -> bytes:
        result = bytearray(self.root + self.parameter + self.rho)
        for secret, nodes in self.fts:
            result.extend(secret + b"".join(nodes))
        for counter, values, nodes in self.layers:
            result.extend(word(counter, 4) + b"".join(values) + b"".join(nodes))
        assert len(result) == SIG_BYTES
        return bytes(result)


def sign(oracle: Oracle, seed: bytes, pk: bytes, cache: bytes, message: bytes) -> bytes:
    assert len(seed) == len(message) == 32 and len(pk) == 16 and len(cache) == CACHE_BYTES
    root, p = cache[:20], cache[20:40]
    if p != parameter_from_seed(oracle, seed) or pk != public_key(oracle, root, p):
        raise ValueError("cache does not match key")
    for trial in range(1 << 20):
        rho = h(oracle, p, 7, seed + message, 0, 0, trial)
        index, leaves = message_index(oracle, p, root, message, rho)
        if leaves[-1] == 0:
            break
    else:
        raise ValueError("digest attempts exhausted")
    fts = []
    fts_roots = []
    for tree in range(FTS_TREES):
        nodes = fts_tree(oracle, seed, p, index, tree)
        fts_roots.append(nodes[-1][0])
        fts.append((fts_secret(oracle, seed, p, index, tree, leaves[tree]),
                    path(nodes, leaves[tree])))
    message_at_layer = fts_root(oracle, p, index, fts_roots)
    layers: list[tuple[int, list[bytes], list[bytes]]] = [None] * 6  # type: ignore[list-item]
    for layer in reversed(range(6)):
        tree, leaf = layer_address(index, layer)
        counter, values = ots_sign(oracle, seed, p, message_at_layer, layer, tree, leaf)
        if layer == 0:
            nodes = cache_path(cache, leaf)
            recovered = ots_leaf(oracle, seed, p, layer, tree, leaf)
            for level, sibling in enumerate(nodes, 1):
                parent = leaf >> level
                recovered = (node_hash(oracle, p, sibling, recovered, layer, tree, level, parent)
                             if leaf & (1 << (level - 1)) else
                             node_hash(oracle, p, recovered, sibling, layer, tree, level, parent))
            if recovered != root:
                raise ValueError("cache path is corrupt")
            message_at_layer = root
        else:
            nodes_by_level = ots_tree(oracle, seed, p, layer, tree)
            nodes = path(nodes_by_level, leaf)
            message_at_layer = nodes_by_level[-1][0]
        layers[layer] = counter, values, nodes
    return Signature(root, p, rho, fts, layers).encode()


def parse_signature(data: bytes) -> Signature | None:
    if len(data) != SIG_BYTES:
        return None
    offset = 0
    def read(n: int) -> bytes:
        nonlocal offset
        value = data[offset:offset + n]
        offset += n
        return value
    root, p, rho = read(20), read(20), read(20)
    fts = [(read(20), [read(20) for _ in range(8)]) for _ in range(FTS_TREES)]
    layers = []
    for height in HEIGHTS:
        counter = int.from_bytes(read(4), "little")
        if counter >= 1 << 20:
            return None
        layers.append((counter, [read(20) for _ in range(CHAINS)],
                       [read(20) for _ in range(height)]))
    assert offset == SIG_BYTES
    return Signature(root, p, rho, fts, layers)


def verify(oracle: Oracle, pk: bytes, message: bytes, witness: bytes) -> bool:
    if len(pk) != 16 or len(message) != 32:
        return False
    signature = parse_signature(witness)
    if signature is None:
        return False
    root, p = signature.root, signature.parameter
    if public_key(oracle, root, p) != pk:
        return False
    index, leaves = message_index(oracle, p, root, message, signature.rho)
    if leaves[-1] != 0:
        return False
    roots = []
    for tree, (secret, nodes) in enumerate(signature.fts):
        leaf = leaves[tree]
        current = h(oracle, p, 9, secret, tree, index, 0, leaf)
        for level, sibling in enumerate(nodes, 1):
            current = (h(oracle, p, 10, sibling + current, tree, index, level, leaf >> level)
                       if leaf & (1 << (level - 1)) else
                       h(oracle, p, 10, current + sibling, tree, index, level, leaf >> level))
        roots.append(current)
    current = fts_root(oracle, p, index, roots)
    for layer in reversed(range(6)):
        tree, leaf = layer_address(index, layer)
        counter, values, nodes = signature.layers[layer]
        digits = digest_encoding(oracle, p, current, counter, layer, tree, leaf)
        if digits is None:
            return False
        endpoints = [chain_walk(oracle, p, value, layer, tree, leaf, chain, digit, 7)
                     for chain, (value, digit) in enumerate(zip(values, digits))]
        current = h(oracle, p, 2, b"".join(endpoints), layer, tree, 0, leaf)
        for level, sibling in enumerate(nodes, 1):
            current = (node_hash(oracle, p, sibling, current, layer, tree, level, leaf >> level)
                       if leaf & (1 << (level - 1)) else
                       node_hash(oracle, p, current, sibling, layer, tree, level, leaf >> level))
    return current == root


if __name__ == "__main__":
    oracle = Oracle()
    seed = bytes(range(32))
    message = bytes(reversed(range(32)))
    pk, cache = keygen(oracle, seed)
    print("keygen", oracle.calls, "calls", oracle.compressions, "compressions")
    before = oracle.compressions
    signature = sign(oracle, seed, pk, cache, message)
    print("sign", oracle.compressions - before, "compressions")
    before = oracle.compressions
    assert verify(oracle, pk, message, signature)
    assert oracle.compressions - before == VERIFY_COMPRESSIONS == 1616
    print("verify", VERIFY_COMPRESSIONS, "compressions")
    assert not verify(oracle, pk, message, signature[:-1] + bytes([signature[-1] ^ 1]))
    offset = 60 + FTS_TREES * (1 + FTS_HEIGHT) * DIGEST
    for height in HEIGHTS:
        changed = bytearray(signature)
        changed[offset + 2] |= 0x10
        assert not verify(oracle, pk, message, bytes(changed))
        offset += 4 + CHAINS * DIGEST + height * DIGEST
    assert offset == SIG_BYTES
    print("signature", len(signature), "bytes")
