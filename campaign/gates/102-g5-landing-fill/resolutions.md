# Gate 102 (#211, G5's landing): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (attached in chat by the user), SHA-256
`14003c5128fc921abce2639ec23365c2f6d477c5c41fb648e3adcd765de568bb`.

**Verdict: HOLD — 0 blockers, 1 major, 1 minor, 5 notes.** No soundness defect.

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Fixed** (the standing rule, WORKFLOW §3: a mechanical re-point in the PR). `tt_forward_run`'s zero-time branch is `not_computesInTime_zero M x _ ((computesInTime_iff M x _ 0).2 ⟨h0, rfl⟩)`. A search of the library for the impossibility's other closing forms (`initCfg_eq, Cfg.init_state` rewrites ending in a contradiction) finds only deterministic sites that already cite the lemma (`DTIME`, `TMSAT`, `CookLevin/Hardness`, `EXPCOM`) and two NDTM analogues (`ExhaustiveReplay`'s private `xr_not_haltsWithin_zero`, an inline step in `NDNormalForm`), which have no published lemma and so are not members; they are recorded in the ledger as a promotion candidate. The sweep's disposition is corrected in this file. |
| 2 | minor | **Fixed.** `two_work_tapes_run`'s sketch states the invariant: each side of a level is empty, half full or full, the two sides of a level hold a constant total, and a rebalance at index `i` restores every level below `i` to half full. |
| 3–7 | note | No change. |

## Round 2 findings (received 2026-11-06)

`findings-r2.md`, verbatim. **Verdict: HOLD: 0 blockers, 2 majors, 0 minors, 4 notes.** Both
round-1 findings are fixed (note 3), and the repair has no soundness defect.

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Fixed outside #211, in #217** (`lean/dedup-nz1`; the standing rule, WORKFLOW §3, and the user's 2026-11-06 ruling on colleague files). `Loop`'s private `emCall_prepared_eval_first` and `Advice`'s `DTIMEAdvice_eq_empty_of_eq_zero` both cite `FinTM.not_computesInTime_zero`; `Loop`'s builds the zero-time computation through `computesInTime_iff` with the actual output. Both sites lie outside #211's one file, and `Loop`'s downstream closure is large, so they ride in the NZ-1 PR. The new search is by kind (`rw`/`simp`/`change … at` with `runFrom_zero`, `runWith_nil`, `initCfg`, `Cfg.init`, `init_state`; zero-case scans; `[] rfl` instantiations; `show`/`change`), and its skipped classes are recorded in the ledger's NZ-1. Round 1's statement that the deterministic fact is cited wherever it applies was false; NZ-1's entry now covers both readings. |
| 2 | major | **Fixed in #217.** The user acknowledged NZ-1 (2026-11-06: publish and re-point now). #217 publishes `Turing.NDTM.not_haltsWithin_zero` (`TuringMachine/Nondeterministic`) and re-points the five NDTM members: the auditor's four (`ExhaustiveReplay`'s private, deleted; `NDNormalForm`'s `hpos`; `NTIME_eq_empty_of_exists_zero`; `AbortDecidesInTime.restart`), plus `BPTIMEThreshold`'s `BPDecidesInTimeWith.one_le`, which the by-kind search found. The ledger's census is corrected (seven sites over both readings). |
| 3–6 | note | No change. |

Round 3 cites #217 (its gate, replay and freeze) and re-checks #211 against it; #211's own file
does not change.

## Round 3 findings (received 2026-11-06)

`findings-r3.md`, verbatim (SHA-256
`79810d06cbe5c45d89316e65c9c96c62985ac681140e3414bef8d7bd409a75e7`). **Verdict: PASS: 0 blockers,
0 majors, 1 minor, 6 notes.** Round 2's two majors are discharged by #217, and #211 is unchanged.
**The gate is CLOSED.** The merge waits for #217 to merge and for a replay of the tree that
contains #211 (`TwoTapes`, `UniversalTlogT`, the facade; note 7).

| # | Severity | Disposition |
|---|---|---|
| 1 | minor | **Fixed in #217**: the same member as gate 108's finding 1 (see gate 108's `resolutions.md`). |
| 2–7 | note | No change. Note 7's merge order is carried into HANDOFF. |
