# Gate 03e (interaction, proof systems, ZK definitions, commitments, NP layer): round 2 resolutions

- **Round:** findings `findings/gate03e-r2-findings.md`, SHA-256 `e32240876e5117c1f080bfaa798706f94bf4e0df613faa300b951e3735d4e20f`; pin `e79397ea`. **0 blockers, 2 majors, 5 minors.** Review `review/gate03e-r2-review.md`: 6 true, 1 partly true (#3); severities kept. Ruling R-03e-r2-1 (A).
- **Repair:** the gate 03 repair batch, PR [#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206) (head `73751f5747d8c0a57aba9939cac8bb16f87ba2ba`, merged by `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; evidence `evidence-repairs/03-batch/`), plus the records commits of 2026-11-06.

| Finding | Severity | Resolution |
|---|---|---|
| #1 | major | **Fixed (records).** DESIGN D8 carries a dated erratum (only GI is statistical; 3COL is computational and cannot be statistical); §5 item 11 is rewritten. No Lean change. |
| #2 | major | **Fixed** (#206, item C). `Protocol.proverBounded_iff` (`Interaction.lean`), `AbortRetry.attempt_eq`, `retry_eq`, `retry_eq_attempt`, `retry_eq_nil` (`Defs.lean`), none `@[simp]`. The 11 sites of the review's M1 table, and 2 more in `GraphIsomorphism/Soundness.lean` and `SoundnessRepGI.lean`, go through `proverBounded_iff`. The seal of the six consumer files on `ProverBounded` passes, and their base versions fail. Prints are in `Checks.lean`. |
| #3 | minor (partly true) | **Fixed (records).** `resolutions-03e-r1.md` rows 5 and M8 corrected. Current counts: 21 `sorry` warnings in the 126-module closure, 18 outside the ZK files (17 `main`'s, 1 `NonUniform`'s). |
| #4 | minor | **Fixed** (ruling R-03e-r2-1 (A), a strengthening). `zk_proof_of_witnessRelation` and `_of_owp` return `LevinReduction L L3COL R R3COL f w p ∧ …`; `zk_proof_of_mem_NP`'s pattern adjusted; docstrings match. |
| #5 | minor | **Fixed.** The repetition convention in `Interaction.lean`'s module docstring is rewritten (the final verifier move carries the verdict; ch. 7 pads each phase with `rounds(|x|)` filler moves). The qualifier is in `GraphIsomorphism.lean` (also its module docstring) and `ThreeColoring/Protocol.lean`. |
| #6 | minor | **Fixed.** `Defs.lean`'s `Lz` necessity paragraph and DESIGN §7 item 51 are narrowed to the 3-colouring protocol (protocols with exactly simulable views are not affected). |
| #7 | minor | **Fixed.** `InteractiveProofs.lean`: the efficiency attribution (Def 116.1's verifier, Def 119.5's prover); the IP scope sentence covers `InteractiveProof`, with the `s = 1` remark on the explicit-error forms; `complete`'s docstring; DESIGN §5 item 8. |
| M1–M5 | (review) | M1, M3, M4, M5: **fixed** with #2, #5, #7 and #3. M2 (tactic-level unfolds in the repair's new proofs): **scheduled** for clean-up part 2 (item C's equation lemmas and `firstHit_eq`). |
