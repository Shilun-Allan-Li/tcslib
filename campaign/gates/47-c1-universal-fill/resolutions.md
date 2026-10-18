# C1-UN: the universal NDTM's three corollaries (PR #129, a fill gate): resolutions (round 1; gate CLOSED)

**Gate:** the fill gate of PR #129 (`lean/c1-un-partial` at `3a1678d1`): BF, H′ and S proved in
`Diagonalization/NTimeHierarchy.lean`; the universal `Turing.exists_timed_universal_NDTM` stays
`sorry` (its pair-extractor contract is #132). Pack `pack.md`; bundle SHA-256
`90165b86eeaa0ac76850cf46effef1ac0e7049b695889ad76c593adc7927b053` (33 sections; folder
`47-c1-universal-fill-gate/`). Replay passed (user, 2026-10-18): 2 of 2, static-equal (2).

**Round 1** (`findings.md`, verbatim): **PASS, 0 blockers, 0 majors, 1 minor, 8 notes.** The
maintainer verified the minor at `3a1678d1`; the notes recommend no change to this landing.
**The gate is closed.** #129 was declared clear to merge (2026-10-18).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The three filled theorems' docstrings still say "spec, fill pending" (lines 175, 311 and 338), and the decider's sketch keeps dated "user decision" and "P3.3 route" narrative. | **True** (`git show 3a1678d1:…NTimeHierarchy.lean`: lines 175 (BF), 311 (H′) and 338 (S) carry "spec, fill pending", while lines 117 (the universal) and 212 (`ntime_hierarchy`) are still correct; lines 73, 124, 181–182 and 247 carry the decision narrative, most of it predating the fill). **Deferred (user, 2026-10-18: "defer and merge tonight").** It rides UN's continuation landing, which edits this file: remove the stale qualifiers and move the process narrative to the records, keeping the mathematical deviations and the remaining dependencies. The module-wide narrative also belongs to the deferred docstring-cleanup pass. |
| 2–8 | notes | Integrity and freeze; BF's route and uniformity; H′'s constant absorption; S's constructibility and domination; the published interfaces and admissions; UN-1's gap is real and #132 supplies it; the static attestations; the execution attestations. | No action. Note 7 carries to UN's continuation brief (use #132's contracts). Note 9's request (bundle the extended probes, seal and admission-walk outputs) carries to the next fill packs. |
