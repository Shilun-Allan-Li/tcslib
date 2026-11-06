# Gate 110 (#219, E-PAD statements): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (SHA-256
`fd5005bdb8cb56ba277847b4e0455fe5a61f86487028c8c05bf2ce9ffa30218c`). **Verdict: PASS: 0 blockers,
0 majors, 1 minor, 8 notes.** The statements are true, well-formed and fit their consumer. **The
gate is CLOSED.**

| # | Severity | Disposition |
|---|---|---|
| 1 | minor | **Fixed** (`130b91c3`): the `SpaceComplexity` facade's Contents lists `SpaceComplexity.Padding` (`padLang`, its characterization, and `mem_SPACE_padLang` stated with its proof pending). |
| 3 | note | Optional sanity lemma and citation: deferred to the fill, which may add `pairEncode_mem_padLang_iff` if its proof wants it. |
| 4 | note | Carried into the E-PAD fill brief: account explicitly for initialization and the simulated input; validation in `O(m + 1)`. |
| 7 | note | Carried into Ladner's statement gate: the time bound and the encoding choice (the paired form against the book's `ψ ++ false :: 1^…`) are stated there. |
| 9 | note | The check-8 heuristic (`mem_<def>_iff`) is noted for the lint's maintainer. No change here. |
| 2, 5, 6, 8 | note | No change. |
