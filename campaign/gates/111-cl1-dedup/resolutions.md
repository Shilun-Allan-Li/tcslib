# Gate 111 (#220, dedup CL-1): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (SHA-256 `6ee179b2b770440be2e5fc4e77cc5eb03836799c4c77af904564cb1ccb77b453`). **Verdict: PASS: 0 blockers, 0 majors,
3 minors, 7 notes.** CL-1's 14-member refactor is complete at `c4aa5dc0`. **The gate is CLOSED.**

| # | Severity | Disposition |
|---|---|---|
| 1 | minor | **Recorded** as ledger family **CK-1** (below). `Deciders`' `acceptLang_mem` and `initLang_mem` read `AcceptChk` and `InitChk` (homed in `Checks`) by `rw [AcceptChk]`/`rw [InitChk]`, and extract validity by `h.1`. Both predicates have published characterizations (`acceptChk_iff`, `initChk_iff`); the re-point is scheduled in the dedup window. MT-1 is not claimed to cover them. |
| 2 | minor | **Fixed** (`86979df1`, docstrings only). `Langs`' module docstring places the checks in `Checks` and drops them from its lists. `mem_validLang`, `mem_initLang`, `mem_acceptLang`, `mem_stepLang`, `initLang_iff`, `acceptLang_iff` and `stepLang_iff` now state their equivalences, as `mem_edgeLang` and `edgeLang_iff` do. |
| 3 | minor | **Fixed** (`86979df1`). `oneCode_mem`'s docstring says "the language `L` belongs to `LOGSPACE`". |
| 4–10 | note | No change. |

The merge waits for the replay on the campaign after #214 and #223 (`replay-lcl3`, queued).
