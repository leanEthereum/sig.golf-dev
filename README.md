# sig.golf · rules

Design a **stateless hash-based signature scheme** minimizing `S × C`: signature bytes times maximum honest verification cycles.

## Submission

1. Four RISC-V program images: [keygen](#keygen), [sign](#sign), [expand](#expand), and [verify](#verify), including embedded data.
2. Nonnegative integers `S`, `W`, `K`, and `C`: signature, witness, and cache bytes, and verification cycles.
3. [Six byte offsets](#inputs-and-outputs) specifying where RISC-V inputs and outputs reside in memory.
4. Lean 4 proofs of the [required statements](#required-lean-statements) for those exact images, sizes, layout, and bound.

Submit each image as `submission/images/<program>.code` (little-endian 32-bit instruction words) and `submission/images/<program>.data` (raw embedded bytes). All eight files are required; empty files are allowed. The verifier generates `SigGolf.Images` from these bytes and additionally requires `SigGolf.Challenge.images_match : submission.image = SigGolf.Images.images`. This equality is kernel-checked alongside the certificate; candidate evaluation is never used to choose the published images. The verified source snapshot includes the image files. See [the submission guide](site/llms.txt) for the other files and theorem names.

## Parameters

| Constant          |                 Value |
| ----------------- | --------------------: |
| `BUDGET_KEYGEN`   |     2^20 compressions |
| `BUDGET_SIGN`     |     2^17 compressions |
| `BUDGET_EXPAND`   |     2^20 compressions |
| `FAILURE`         |                2^-128 |
| `LIFETIME`        | 2^32 signing requests |
| `SECURITY_BITS`   |                   127 |
| `CYCLE_LIMIT`     |           2^32 cycles |
| `MAX_PROGRAM_BYTES` |            2^20 bytes |

Every object has a fixed size in bytes:

| Object     |                           Bytes |
| ---------- | ------------------------------: |
| Message    |                              32 |
| Secret key |                              32 |
| Public key |                              16 |
| Cache      |           `K` (maximum 128 KiB) |
| Signature  |           `S` (maximum 16 KiB) |
| Witness    |           `W` (maximum 128 KiB) |

## Programs

### keygen

Derives the public key and a public, untrusted cache from the secret key.

- **Inputs:** secret key.
- **Outputs:** public key and cache, or failure.
- **Context:** enclave.

### sign

Produces a compact signature for a given message.

- **Inputs:** secret key, cache, message.
- **Outputs:** signature or failure.
- **Context:** enclave.

Suggestion: the cache is untrusted, so a tampered cache must not leak secrets or aid a forgery. A MAC prevents this: keygen stores H(domain separator ‖ secret key ‖ rest of the cache) in the cache, and sign checks it.

### expand

Converts the signature into a verification witness.

- **Inputs:** message, public key, signature.
- **Outputs:** witness or failure.
- **Context:** prover host.

Example: It may restore pruned Merkle paths or copy the signature when `S = W`.

### verify

Checks whether the witness authenticates the message under the public key.

- **Inputs:** message, public key, witness.
- **Outputs:** accept or reject.
- **Context:** zkVM.

## Model and costs

### Random oracle

All programs and the [security game](#security)'s adversary share one random oracle H, mapping each input of 64·k bytes (k ≥ 1) to an independent uniform 32-byte answer. Security is proved in Lean in this model and counts calls to H.

### RISC-V programs

Each program is an [RV64IM](#risc-v-interface) program with one extra instruction, `HASH(input, n, output)`, issued as a [system call](#system-calls). It reads n bytes starting at address `input`, queries H on them, and writes the 32-byte answer at address `output`. The input and output addresses must both be multiples of 8, and n must be a nonzero multiple of 64. Hashing n bytes costs `n / 64` compressions.

| Operation                                                                                                       | Cost                                                   |
| --------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------ |
| Ordinary instruction                                                                                            | 1 cycle                                                |
| Multiplication or division: `MUL`, `MULH`, `MULHSU`, `MULHU`, `DIV`, `DIVU`, `REM`, `REMU`, and their `W` forms | 4 cycles                                               |
| HASH                                                                                                            | 8 cycles per compression (no extra instruction charge) |
| HALT                                                                                                            | 1 cycle                                                |

Verification also pays for its witness: `⌈W / 256⌉` cycles.

## Required Lean statements

### Honest experiment

For any `secretKey`, `message` and oracle H, consider the following experiment:

1. `keygen(secretKey)` returns the `public key` and `cache`.
2. `sign(secretKey, cache, message)` returns the `signature`.
3. `expand(message, public key, signature)` returns the `witness`.
4. `verify(message, public key, witness)` returns the verdict.

Stop at the first failure. We say the `experiment succeeds` when all stages succeed and verification accepts.

`N_P` counts program P's compressions; it is zero if P is never reached. `BUDGET_P` denotes P's named budget.

1. **Completeness** ([Lean statement](SigGolf/Statements.lean#L21-L24)): for every secret key, `Pr_H[experiment succeeds for every message] >= 1 - FAILURE`.
2. **Compression budgets** ([Lean statement](SigGolf/Statements.lean#L26-L31)): for every secret key and P in {`keygen`, `sign`, `expand`}, `E_{H,M}[2^(N_P / BUDGET_P)] <= 2`.

`Pr_H` is over H; `E_{H,M}` is over an independently sampled random oracle H and uniform 32-byte message M.

**Remark.** After H is fixed, selected messages may cost much more than this average, even if the message is chosen in advance. Hashing a message with a secret-derived salt is a scheme-dependent mitigation, not a proved adaptive cost bound. A deterministic salt repeats on repeated messages. The current rules do not guarantee fast signing for adversarially chosen messages.

3. **Verification cycles** ([Lean statement](SigGolf/Statements.lean#L33-L38)): for every secret key, message and oracle, if the experiment succeeds, [`verify`](#verify)'s cycles plus the witness charge `⌈W / 256⌉` are at most [`C`](#submission).

### Security

Consider the following experiment for a classical probabilistic adversary `A` with unrestricted computation and an integer hash-call budget `Q >= 1`:

1. Sample H and a uniform secret key independently. Initialize an empty transcript T and count all calls to H throughout the experiment.
2. Run `keygen(secretKey)`. Failure ends the experiment without a win; otherwise give `A` the public key and cache.
3. `A` may then adaptively query two oracles:
   - **`random_oracle(input_A)`:** for an `input_A` of 64·k bytes, return H(input_A).
   - **`signing_oracle(message_A, cache_A)`:** run `sign(secretKey, cache_A, message_A)` using the original secret key. Return the signature or failure. Add each returned `(message_A, signature)` to T. Allow at most `LIFETIME` requests.
4. `A` makes one final submission, choosing either form below:
   - **witness weak unforgeability:** submit `(message_A, witness_A)`. `A` wins if `verify(message_A, public key, witness_A)` accepts, and no pair in T has message `message_A`, and the total hash-call count is at most Q
   - **signature strong unforgeability:** submit `(message_A, signature_A)`. `A` wins if `expand(message_A, public key, signature_A)` returns a witness that `verify` accepts, and `(message_A, signature_A)` is not in T, and the total hash-call count is at most Q.

The total hash-call count includes key generation, signing, `A`’s queries, and final expansion and verification when performed.

**Security** ([Lean statement](SigGolf/Statements.lean#L40-L45)): for every A and `Q >= 1`, `Pr[A wins] <= Q / 2^SECURITY_BITS`, over the secret key, H, and `A`’s private randomness.

### Termination

**Termination** ([Lean statement](SigGolf/Statements.lean#L47-L51)): every program terminates with a result or failure in fewer than `CYCLE_LIMIT` cycles, for every input and oracle.

## RISC-V interface

Use [RV64I](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv64.html) and the [M extension](https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html).

Each program satisfies **`4 × instruction count + embedded-data bytes < MAX_PROGRAM_BYTES`**.

### Code and memory

Code occupies a separate, immutable instruction address space. Instruction i is at `0x1000 + 4 × i`.

Memory occupies `0x000000`–`0xFFFFFF` (16 MiB).

Load D embedded bytes at `data_base = 16 × floor((0x1000000 - D) / 16)`. Initially, `sp = data_base` and `PC = 0x1000`; all other registers are zero.

### Inputs and outputs

Each submission specifies six byte offsets, shared by all four programs: δ<sub>message</sub>, δ<sub>secret key</sub>, δ<sub>public key</sub>, δ<sub>cache</sub>, δ<sub>signature</sub>, and δ<sub>witness</sub>. Each gives the memory address where that object is written or read. The buffers have the sizes in [Parameters](#parameters), start at 8-byte-aligned addresses, do not overlap, and end at or below `data_base` for every program.

Before each execution, memory is zero except for embedded data and the inputs listed under [Programs](#programs); unused object buffers remain zero.

Example: before [`sign`](#sign), write the secret key, cache, and message at their offsets. On success, read the signature at δ<sub>signature</sub>.

HALT ends execution with exit code `a0`: `0` means success and any other value failure. For [`verify`](#verify), these mean acceptance and rejection, respectively.

### System calls

ECALL selects one of two services through `t0`:

| `t0` | Service | Arguments                                                                 |
| ---: | ------- | ------------------------------------------------------------------------- |
|    0 | HASH    | `a0 = input address`, `a1 = input length in bytes`, `a2 = output address` |
|    1 | HALT    | `a0 = exit code` (0 = success)                                            |

HASH writes H's 32-byte answer at the output address. Any other `t0` fails.

### Further Details

- **Proof checking:** the certificate must pass Lean’s kernel against the organizer’s definitions. Its transitive axiom dependencies may contain only `propext`, `Classical.choice`, and `Quot.sound`.
- **Instructions:** encodings are 32 bits. Fetching outside the code or at a non-4-byte-aligned address fails. `FENCE` has no effect; `EBREAK` fails.
- **Registers:** `x0`–`x31` are 64 bits. `x0` always reads zero and ignores writes. Aliases are `sp = x2`, `t0 = x5`, and `a0`–`a2 = x10`–`x12`. PC is separate.
- **Memory access:** addresses count bytes; multi-byte integers are little-endian. Accesses of 1, 2, 4, or 8 bytes require alignment to their size. Misaligned accesses fail.
- **Bounds:** every memory access and buffer must fit completely in memory. For unsigned byte address p and length n, require `p + n <= 0x1000000`. Instruction arithmetic and effective-address calculation follow RV64IM.
- **HASH arguments:** addresses and byte length n are unsigned 64-bit values. The input and output addresses must both be 8-byte aligned, and n must be a nonzero multiple of 64. The input’s n bytes and the output’s 32 bytes must fit entirely in memory.
- **HASH execution:** read the n input bytes in increasing address order; they are H’s input. Read all input before writing the answer, so buffers may overlap. Preserve registers and advance PC by 4.
- **Faults:** an encoding outside RV64IM (such as compressed, A, F, D, CSR, or `FENCE.I`), invalid HASH arguments, or any other fault ends the run as a failure; for `verify`, a rejection.

## Lean project

[`SigGolf.Certificate submission C`](SigGolf/Statements.lean#L53-L60) in [SigGolf/Statements.lean](SigGolf/Statements.lean) is the competition claim for the exact four program images and declared sizes. Besides the five statements above, it contains [`Admission`](SigGolf/Statements.lean#L12-L16): the size maxima, the program size limit, and the buffer layout rules. [SigGolf/Security.lean](SigGolf/Security.lean) defines the attacker and both forgery experiments; [SigGolf/Riscv.lean](SigGolf/Riscv.lean) defines execution and costs. In Lean, the adversary is an `OracleComp` over coins, H, and the signing oracle: a computation that makes finitely many queries and then submits a forgery or gives up. A strategy that could run for ever is represented by its truncations, which give up where they are cut. Giving up never wins, and such a strategy's win probability is the limit of its truncations', so the bound over all adversaries bounds every adaptive strategy.

Build the statements and regression checks with `lake build SigGolf SigGolfTests`. Dependencies are pinned in `lake-manifest.json`. These files define the requirements; they do not certify a particular signature scheme. Submissions are verified from the [sig.golf-submissions](https://github.com/leanEthereum/sig.golf-submissions) repository.

Verification intake admits at most 1000 entries, 8 MiB per file, and 16 MiB total including images; no symlinks or alternate Lean module headers. Proof checking allows 4 hours, 24 GiB, and two CPUs. On Linux, writable build output is limited to 4 GiB and 100,000 inodes; `/tmp` and `/var/tmp` each have 256 MiB and 16,384 inodes, and `/dev/shm` has 64 MiB and 4,096 inodes. These temporary filesystems count toward the memory limit; dependencies are read-only.

## Known limitations

- **Practical cycle limits (unresolved):** compression budgets do not count ordinary instructions. Keygen, sign, and expand are only subject to the universal `CYCLE_LIMIT`, so these rules do not establish hardware-wallet performance. Separate practical cycle limits and adaptive-message cost guarantees remain organizer decisions; no new limits are imposed here.
- **Timing and other side channels:** the adversary receives signatures or failure, not execution time, memory accesses, or internal hash traces. A certificate does not establish constant-time execution or side-channel resistance.
- **Untrusted verification inputs:** `C` bounds successful honest verification. Arbitrary witnesses, including other accepting witnesses, are covered only by `CYCLE_LIMIT`, not by `C`.
- **Whole-experiment security accounting:** honest hash calls count toward `Q` too. Adding unnecessary honest hashing increases the allowed forgery probability at the resulting budget. The bound is not an attacker-only work estimate.
- **Quantum security:** the security game only considers classical adversaries. NIST level 1 requires ≈ 64 bits of security against quantum adversaries.
- **Single-user security:** the security game targets a single key, but a real attacker can target many users at once. The standard defense starts every hash with a per-key public parameter, so work against one user is useless against others. Drake's trick makes this cheap: a 16-byte parameter in the public key, padded with 48 zero bytes, fills the first 64-byte block of every hash, so its hash state is computed once and reused. Multi-user security then costs one compression and 16 bytes of public key.
- **MPC for threshold signing:** threshold signing runs keygen and sign inside multi-party computation (MPC), where hashing secret data costs far more. MPC precomputation followed by grinding on public values at signing can help (see [RivaLabs](https://github.com/RivaLabs-Core)).
- **Trading lifetime for faster keygen and signing:** [hypertree pruning](https://conduition.io/cryptography/hypertree-pruning/) replaces most hypertree leaves with cheap placeholder hashes and grinds the randomizer until each message lands on a kept leaf, which speeds up keygen and signing without changing verification but lowers the safe number of signatures.
- **Choice of hash function:** the oracle H takes inputs made of 64-byte blocks, returns 32-byte answers, and costs one compression per block. This cost model is accurate for BLAKE2s, for BLAKE3 on inputs up to 1 KiB, and for the SHA-256 compression function, but less precise for standard SHA-256, whose padding adds a block to every input, and for SHA-3, which absorbs 136 bytes per permutation.
- **Choice of ISA and metering:** RV64IM, the [cost of each instruction](#risc-v-programs), and details such as [where HASH reads its inputs](#system-calls) are one choice among many, and may not match a given zkVM.
- **Delegating hashes of public values:** the budgets assume the enclave, such as a hardware wallet, computes every hash. Hashes of public values, typically for grinding, could be offloaded to a powerful host, possibly with a SNARK proving correctness.
- **127 bits of security:** schemes built on 128-bit hash digests, such as SLH-DSA's 128-bit parameter sets, reach 127 bits of security rather than 128: an adversary can try to guess second preimages, and this bound is tight. [This note](https://github.com/leanEthereum/leanVM/releases/download/doc-latest/SPHINCS.pdf) gives a security proof and a matching attack.
