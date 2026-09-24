# Compact SPHINCS candidate (local work)

This is not a beta submission yet. The abstract 24-tree scheme has a Lean security and completeness proof, and `SigGolfCandidate/SphincsWire.lean` fixes a 11,324-byte signature/witness format with a 16-byte committed public key. The four-byte encoding of each 20-bit counter must reject nonzero high bits.

`reference.py` exercises keygen, cache-assisted sign, expand-by-copy, and verify with SHA-256 as a deterministic test oracle. `build_images.py` assembles all four RV64IM images in `SigGolfCandidate/SphincsImages.lean`; `SigGolfCandidate/SphincsSubmission.lean` fixes their common layout and proposed score and proves static admission for the exact images. `check_verify.py` compares expand and verify to the reference. `check_keygen.py` verifies the complete keygen image and exact 128 KiB cache; it measured 997,377 compressions and 91,795,978 cycles. `check_sign.py` matches the entire 11,324-byte signature and checks rejection of selected cache corruption; its run used 104,341 compressions.

The verifier uses 1,616 HASH compressions on an accepting run. Differential tests observe `159,530 + r` executed instructions and `171,173 + r` cycles, where `r` is the number of right turns across 192 FORS and 34 hypertree nodes. Thus the candidate cycle bound is 171,399 and its proposed score is 1,940,922,276. These figures still need a proof about the exact image; tests alone do not certify them.

Remaining work is a formal correspondence between all four images and the abstract scheme, resource and termination proofs, and a security reduction for the 16-byte public-key commitment and attacker-controlled cache. None of this branch should be pushed as a normal submission until the complete `SigGolf.Certificate` passes.
