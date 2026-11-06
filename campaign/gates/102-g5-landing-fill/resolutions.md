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
