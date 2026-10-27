# H, the nondeterministic time hierarchy (PR #172, a fill gate): resolutions

**Gate:** the fill gate of PR #172 (`lean/h-hierarchy-landing` at `33d68537`). Pack `pack.md`;
bundle SHA-256 `bd5976719f5fd2c0d02c5c89e5b10084f2f84ac959ffbfcf858889dfac29fb3d` (54 sections),
the records at `3190c6be`. **Findings** (`findings.md`, verbatim, SHA-256 `e7ecff3c…`; received
2026-10-27): **PASS, 0 blockers, 0 majors, 1 minor, 18 notes.** The gate is closed.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The ledger's family censuses need a pinned-tree denominator and a cumulative total: `Nondeterminism` has 201 declarations at `33d68537` (199 is after #171), and `NTimeHierarchy` carries two members across RS-1 and TR-1, 2 of 25. | **True; corrected** in `campaign/duplication-ledger.md`. Every census now names its tree: RS-1 at #170's head and the tip before #172, TR-1 at #172's head, PL-1 at #171's head. TR-1 gives `Nondeterminism` 1 of 201 at `33d68537` (8 public, 193 private; 1 of 199 after #171). Its new cumulative line gives `NTimeHierarchy` 2 of 25 (8.0%) after #172, RS-1's `un_setup` and TR-1's `nh_accepts_of_halts`. The counts were re-taken with `declfreeze.py` v4 at both trees. No file reaches one fifth. The promotions and re-points stay in the dedup window (12.2c). |
| 2 | note | Integrity and landing scope verified. | Agreed. |
| 3 | note | The language and time semantics are faithful; totality is universal over branches. | Agreed. |
| 4 | note | The schedule definitions have the required endpoint convention and repeat each code. | Agreed. |
| 5 | note | Constructibility and coded-machine packaging add no hidden monotonicity or totality. | Agreed. |
| 6 | note | Inclusion holds without monotonicity; the declared deviations remain explicit. | Agreed. The module docstring states the two addends and the `g + 1` conclusion. |
| 7 | note | One late stage discharges all three thresholds in the right quantifier order. | Agreed. |
| 8 | note | The chain consumes the contracts exactly and proves strictness. | Agreed. |
| 9 | note | Truncation and the decider's reading are correct, using universal halting. | Agreed. |
| 10 | note | Boundary and degenerate cases hold; keep the truncation's boundary cases when its API is published. | Agreed. TR-1's disposition (the public truncation beside `AcceptsWithin.mono`) will carry the two cases, `t ≤ T` by padding and `t > T` by the halted prefix. |
| 11 | note | The normal-form contract is plausible as stated and used at its stated strength. | Agreed; it stays `sorry` until its own fill. |
| 12 | note | The diagonalizer contract's uniform and per-code bounds are consistent. | Agreed; E-Q (now landing in #173 and its continuation) and E-D fill it. |
| 13 | note | Rule 10 is satisfied by the changed proof. | Agreed. |
| 14 | note | The screen reproduces byte-for-byte; no published API is bypassed. | Agreed; TR-1's promotion is scheduled, and finding 1 is corrected. |
| 15 | note | The freeze and the constant-fold refactor are verified; the raw "UNAUTHORIZED" labels come from running without an allowance list. | Agreed. |
| 16 | note | The rewritten text matches the proof; the brief review's F1–F10 leave no gap. | Agreed. The unissued brief and its megafill cover stay as records only. |
| 17 | note | Both lint attestations reproduce. | Agreed. |
| 18 | note | The elaboration evidence is consistent; not kernel-replayed by the auditor. | Agreed. The replay (below) is the independent elaboration. |
| 19 | note | Run the downstream replay on the combined tree before merging, with fresh axiom walks. | Agreed; it is #172's merge condition. |

**The replay** (pending): `NTimeHierarchy` now imports `NTimeDiagonalizer`, which #173 (E-Q's
checkpoint 1) changes. So the replay is written by `mk-next.sh` once #173 merges, chained from
`oleans-leqcp1`, with the headline axiom prints and the sorry walk on that tree.

**Merge state. #172: not yet clear to merge** (2026-10-27): the gate is passed; it waits for #173's
merge and then its replay.
