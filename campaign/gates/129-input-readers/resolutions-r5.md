# Gate 129 round 5 resolutions for #251

Round 4 held the exact source at `39dfa843b02ae7fdd0acaeacfadf5bba17a60feb`.
Seyoon selected Codex for this follow-up. The prior approvals cover the four
non-simp readers, the Convention and Reductions imports, and the existing
Primitives factoring. Round 5 uses the existing equations and private proof
reuse for the following findings.

| Finding | Resolution |
| --- | --- |
| 1 · major · no-write fields | `apply_workTape_of_no_write` now supplies the right-blank work field in `rawStrip_computes`, candidate tape zero at overflow in `splitRestore_append`, every tape in the setup and emit rows and the nonblank loop row in the polynomial controller, and the two inactive banks at each live copy row in the candidate and suffix preparation proofs. The nearby closing-form sweep also routes exact no-write fields in the polynomial administrative move, the length checker, the forwarding parser and payload frame, and the counted-source candidate tape through the same lemma. |
| 2 · major · complete action equation | The exact `Action.apply.eq_1` equation supplies all 21 former uses of the private Catalog wrapper, which is removed. The full record computation in `controlAction_apply` now cites `controlAction_def` and `Action.apply.eq_1`. Round 4's historical pair 155 fell below the 60-character cutoff when its Primitives donor was shortened. Simulation's proof remained byte-identical in that round. The actual Simulation replacement is in the round 5 patch. |
| 3 · major · copy and halt | The empty token case reaches the suffix-copier entry after two separator emissions and cites `scanCopy_suffix` with an empty unread word. The final separator row is shared with the nonempty case. The complete prepender run cites `scanCopy_finish` after emitting its fixed prefix. `prependTM_computes` and the empty-input constant-source specialization share that run. The two unused private prefix-copy and halt proofs are removed. The suffix and finish lemmas move earlier in Primitives with exact source bytes. |
| 4 · minor · branch state witness | `splitBody_round` proves the common live-state witness before the branch split and uses it in both branches. |
| 5–8 · notes · retained repairs | The round 3 and round 4 reader repairs and earlier copy, rewind and word-seam re-points are covered by the exact source comparison and current whole-proof checks. |
| 9 · note · source and proof evidence | See the new source freeze, complete boundary metadata, paired controls, candidate sweep and copy dispositions for the current round. |
| 10 · note · replay | See the fresh dependency-ordered merged-tree replay and per-module source, log and object receipts for the current round. |

The no-write lemma assumes an outer `none`. The remaining write rows
preserve their existing action proofs, including the `some none` erasures.
Administrative writes to a separate head vector in the polynomial controller
are also a different case. The sweep inventories candidates and checks the
actual transition premises. It is bounded to the audited families and the
specified source population.

The current PR head is `c2fbacf42718b16c03fc0e61b571a9cf2f8c6ecb`, and the campaign Lean base is `ef98f1685ddfb8da40d8e97890c0fff6d145523b`.
The 395-module merged-tree replay passed with all 65 inherited admissions
in byte-identical source files. All 125 whole-proof checks and 78 paired
controls passed. The copy review reports 197 current span
dispositions and records the round 4 comparison separately.

## Round 5 result (2026-11-12)

Codex returned **CLEAR (0 blockers, 0 majors, 0 minors, 11 notes)**,
recorded verbatim as `findings-r5.md` (SHA-256 `92085b2842295179dc936bf6dd7468d3419047901505321d75bc154688906248`).
Notes 1–4 confirm the four round 4 repairs. Notes 5–8 confirm the retained
reader repairs and approvals. Notes 9–11 reconcile the bundle, the fresh
cloud replay and the copy accounting. None needs action. **Gate 129 is closed.**
