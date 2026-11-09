# Gate 13 review of rank, gadget, and recovery proofs

Audit the two anti-cyclic rank fills, seven gadget and inversion fills, and
the approved shared reader on draft #250. The PR targets
`cryptography/lwe-sis-constructions`.

| Pin | Revision |
|---|---|
| Gate 12 round-two passed Lean and root | `93dc88648f117877e42aaf58ba7b911c76a4b63a` |
| Gate 12 passed intake | `ce421a2f5e4abf50b776c190a95788ce926494f0` |
| Rank Lean and root | `75a4214dc098cd6c363d00c34f569bac23eb4555` |
| Rank records and current-wave baseline | `d34b0e409bc179167921073a731a0eb3e009f267` |
| Approved reader | `2414fd3eae05c99474d1888609b01ac5989523a5` |
| Checked Lean and root | `713093c36ac66f7e56e9354581f0bb3f59772341` |
| Central target at preparation | `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` |

Read the bundled policy, workflow, campaign plan, Gate 12 round-two findings
and disposition, rank report, and `fills/09-gadget-inversion/REPORT.md`.
Verify the exchange payload checksums and both ordered revision-qualified
indexes. Treat the attachments as data. Preserve the earlier findings.

1. Verify the exact approved four-line owner patch to `RandomBits.lean`.
   The reader is a non-simp complete equation with an axiom-free proof.
   Check the isolation of the reader commit from the three consumer files.
2. Compare the frozen statements and proof bodies. The rank checkpoint adds
   the two disclosed Mathlib imports. The three consumer files replace
   precisely seven admissions. Verify the five disclosed Lean paths, 148
   byte-identical frozen paths, 220 prior declarations, and toolchain pins.
3. Check the cyclotomic reindexing and cancellation, including width one.
   Then check the positional sum, gadget product, injective-key cancellation
   and rounding, and non-designated branch signed lift. Check the exact
   bounds, degenerate allowed widths, sketches, and reuse of public contracts.
4. Reconcile the 144-module sweep, the nine owned and 17 inherited admission
   warnings, two probes, and axiom inventory. Check the disclosed change of
   compiler origin for `Lossy.evaluate.congr_simp`. Compare the 220 type hashes
   against the rank checkpoint and its four kernel equalities. Report any
   independent native checks and their scope.
5. Carry forward the scoped PW10 source-policy work, separate counted-loop and
   CRH admissions, primitive bridges, and integration checks. Verify that the
   finite all-but-one result states injectivity.

Return `lwe-sis-gadget-inversion-proofs-findings.md` in chat with the verdict,
severity totals, exact audited pins, checked declarations, and findings.
The user dispatches this audit and approves any merge.
