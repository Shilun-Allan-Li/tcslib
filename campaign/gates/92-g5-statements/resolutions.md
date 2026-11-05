# G5's statements (PR #189, a statement gate): resolutions

**Staged (2026-11-04):** `pack.md`, at #189's head `2339d2df`. Bundle `92-g5-statements-bundle.md`,
SHA-256 `8fbe17172056ae669d35253e70b77f3bc31d1abc1fd3c37fa294dad2578cd954` (257 sections), the records at
`48275d52`; in the exchange `arora-barak-ch3-4/outbox/gates/92-g5-statements-gate/`. `replay-lg5` running.
**Dispatched (user, 2026-11-04);** the folder archived.
**`replay-lg5` passed** (2026-11-04): 325 of 325 at `2339d2df`, 0 failed, static-equal (73, all pre-existing); snapshot `oleans-lg5`.

**Round 1** (`pack.md`, head `2339d2df`). **Findings** (`findings.md`, verbatim, SHA-256
`7e55640611312b810b5629b84e9b9d5a4c345023904e2692291bdaec1ef092b5`; received 2026-11-04): **DO NOT CLOSE, 0
blockers, 1 major, 3 minors, 6 notes.** The statements are sound, including the boundary cases;
the remaining Hennie–Stearns admission is authorized for this statement gate.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | `two_work_tapes_binary` reads `FinTM.ComputesFunInTime` by reduction (rule 10), and the seal did not cover it. | **True; fixed** (`caa6bf53`): the hypothesis and the conclusion pass through `computesFunInTime_iff`. The seal gains a fifth copy, `TTSealed`, with `FinTM.ComputesFunInTime` sealed: 15 definitions, 5 copies, controls 30/30 unsealed and 0/30 sealed (`evidence/round2/rule10/`). |
| 2 | minor | `FinTM.stateEquivFin` lacks an equation (policy §1, check 8). | **True. Ruled (user, 2026-11-04): fix all now.** `FinTM.stateEquivFin_eq`, its defining equation (`rfl`); check 8 no longer lists it. |
| 3 | minor | "The converse cannot say more" overstates the limitation. | **True; reworded** as the auditor proposed: without an image hypothesis the converse cannot in general assert `o = w.map e`. |
| 4 | minor | The bundle lacked the replay's log. | **True:** `replay-lg5` passed after staging (325/325; `evidence/merged-tree/`, now with its log). Round 2's replay is `replay-lg5b`. |
| 5–10 | note | Integrity and freeze; the two-tape contract; the coding semantics; `universal_TlogT`'s relaxed quantifier; axioms and seals; homes, screen, names, lint. | Agreed. On note 9, `universal_TlogT` is not claimed admission-free: it reaches `sorryAx` through `two_work_tapes_run` until G5's fill. |
