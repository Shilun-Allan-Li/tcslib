# Final explicit acceptance-reader correction

Lead-owned canonical C_A found one foreign-definition access in
ContinuationProbability.acceptProb_prod: its initial acceptProb_def rewrite affected the
outer occurrence, while the RHS occurrence inside uexp was left for the final rfl to
unfold. The full old seal failure is preserved by the lead at
evidence/logs/final-seals-stream-2/final-coe-SealA_Cryptography_Composability_SequentialZK_ContinuationProbability.log,
reported line155. This was a reader-discipline failure, not a false theorem.

At the lead's request, c changed ONLY that short proof's last line. The final source uses
`simp only [acceptProb_def, Equiv.prodAssoc_symm_apply]`, reading both the RHS acceptance
formula and the product-association equation explicitly. No public statement, import,
other proof byte, frozen file or scope changed. The withV seed-reader correction remains
exactly as checked before. No seal/probe was run by c; lead reruns the affected20 cells.

Old source SHA4b7b7ad15dcd6ead93532c83dfe9e2b1f9750e2d5933ae359949bd7b4475db9a.
First reader-only trial SHA8d631348a0f8e346dcf6df132fa70df0572830978ee140ceb0e48f8a208f7e84
exposed one remaining ordinary native goal: product-association evaluation. Its complete
source/patch/roundtrip and raw native failure remain,2.69s actual runtime,
maxRSS2,238,791,680bytes. No interruption, timeout or resource exception.

Final source SHA91355ac3dff34e7b06e8684bf36b1c5fb363c7688a737f8f4efcf4f18246011d,
354lines/max94columns. Adding the published product-association reader closes the same
proof. Native retry02 passed0errors/0warnings,2.42s actual runtime,
maxRSS2,246,049,792bytes. All output/source/result evidence is preserved; final patch and
roundtrip-final.json verify exact forward/reverse git-apply bytes and that replacing only
that final line by the old rfl restores every old source byte, including all statements.

Both native attempts used seq-zk-c, the shared Lean slot wrapper, the private c olean tree,
/usr/bin/time -l and scripts/lean_check_tree.sh for this module alone. No Lake, dependent
sweep, seal, axiom probe, new definition, theorem or Mathlib root. All171 prior current
receipt files were verified unchanged. Source and this new evidence are closed for exact
copying into the lead's final revision6 matrix/payload.
