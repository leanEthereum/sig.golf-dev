# Compact SPHINCS candidate (local work)

This is not a beta submission yet. The abstract 24-tree scheme has a Lean security and completeness proof, and `SigGolfCandidate/SphincsWire.lean` fixes a 11,324-byte signature/witness format with a 16-byte committed public key. The four-byte encoding of each 20-bit counter must reject nonzero high bits.

`reference.py` exercises keygen, cache-assisted sign, expand-by-copy, and verify with SHA-256 as a deterministic test oracle. `build_images.py` assembles all four RV64IM images in `SigGolfCandidate/SphincsImages.lean`; `SigGolfCandidate/SphincsSubmission.lean` fixes their common layout and proposed score and proves static admission for the exact images. `check_verify.py` compares expand and verify to the reference. `check_keygen.py` verifies the complete keygen image and exact 128 KiB cache; it measured 997,377 compressions and 91,795,978 cycles. `check_sign.py` matches the entire 11,324-byte signature and checks rejection of selected cache corruption; its run used 104,341 compressions.

`SigGolfCandidate/SphincsExpansion.lean` and `SigGolfCandidate/SphincsExpandCopy.lean` prove that the exact expand image returns the input signature byte-for-byte in 8,500 cycles with no hash calls. Their axiom checks show only Lean's standard axioms.

`SigGolfCandidate/SphincsSecurity/Proof/Adversary/Security128.lean` strengthens the deterministic-seed scheme's internal forgery bound to Q / 2^128 for Q ≤ 2^127. This leaves a separate Q / 2^128 allowance for the 16-byte public-key commitment. It does not yet establish the submitted bytecode's security claim.

`SigGolfCandidate/SphincsCommitment.lean` proves that the commitment input uniquely encodes the internal public key and cannot coincide with any key-derivation, nonce-generation, or verification hash input. It also proves that a fresh 256-bit oracle response matches a fixed 16-byte commitment with probability 2^-128. An adaptive collision bound and the game reduction to the actual four bytecode programs remain open.

`SigGolfCandidate/SphincsCache.lean` specifies the public top-tree cache rows. Lean proves each row immediately follows the preceding one and every authentication sibling fits inside the 81,940-byte used prefix of the 128 KiB cache. A check of all 22,528 leaf/level sibling offsets against the executable reference confirms the same locations; the bytecode's use of this layout still needs proof.

`SigGolfCandidate/SphincsBridge.lean` proves the abstract byte-string oracle inputs pack injectively into the organizer's length-tagged bit-vector queries, preserving commitment domain separation. `SigGolfCandidate/SphincsVerifierCommitment.lean` proves the exact verifier entry jump reaches `0x1010`, identifies the first HASH instruction at `0x1130`, and shows that a state satisfying the prepared-input invariant sends the correct 60-byte commitment query for eight cycles. Establishing that invariant across the intervening straight-line instructions is still open.

`SigGolfCandidate/SphincsVerifierPrefix.lean` exposes a checked 77-word prefix of the exact image. `SigGolfCandidate/SphincsVerifierSlots.lean` proves the entry jump and the next 16 instructions execute, zeroing all four commitment-header scratch words. This is the start of the missing straight-line refinement, not a proof of the entire prefix.

`SigGolfCandidate/SphincsVerifierCopy.lean` extends the exact execution trace through instruction 31: it sets the witness and hash-buffer pointers, then executes all five load/store pairs for the first 20-byte commitment field. `SigGolfCandidate/SphincsVerifierCopyMemory.lean` proves that the five resulting 32-bit destination words equal the corresponding witness words, with only Lean's standard axioms. Connecting those words to the typed commitment input and following the remainder of the verifier are still open.

`SigGolfCandidate/SphincsVerifierCopyParameter.lean` extends the exact trace through instruction 45, including the second 20-byte copy. `SigGolfCandidate/SphincsVerifierCopyParameterMemory.lean` proves that copy reproduces the witness parameter and leaves the copied root words intact. The header and HASH register setup before the first oracle call remain to be certified.

The verifier uses 1,616 HASH compressions on an accepting run. Differential tests observe `159,530 + r` executed instructions and `171,173 + r` cycles, where `r` is the number of right turns across 192 FORS and 34 hypertree nodes. Thus the candidate cycle bound is 171,399 and its proposed score is 1,940,922,276. These figures still need a proof about the exact image; tests alone do not certify them.

Remaining work is a formal correspondence for keygen, sign, and verify with the abstract scheme, their resource and termination proofs, and a security reduction for the 16-byte public-key commitment and attacker-controlled cache. None of this branch should be pushed as a normal submission until the complete `SigGolf.Certificate` passes.
