# Gate 12 · resolutions, round 1

**Round 1: HOLD** (0 blockers, 1 major, 2 minors). Auditor Codex, 2026-11-11; findings uploaded by
Seyoon and filed verbatim in [findings/](findings/gate12-cpa-pilot-findings.md) (SHA-256
`8d33edf17d26349eafd7e2916c6102be5d721a2d0edb0fc039573cf33cc032a2`). The auditor found no false
statement and no missing hypothesis; the headers need no change.

| Input (round 1) | Pin |
|---|---|
| Exchange | `2b8a52de306d6d2bd097887d6cfc6a173479aca9` |
| Lean head | `135d54511dc0e5c42d93d1d680bf1f26c6aba5cc` |
| Records | `8e8bc7672630a99abb9fee646006357d4153bacb` |

| # | Severity | Resolution |
|---|---|---|
| G12-01 | major | **Fixed (evidence).** Confirmed: the round-1 replay ran before the final docstring wrap of `AdaptiveCPA.lean` (row hash `f036d2ce…`), and the wrapped file was rechecked by direct checker calls that were not logged. Round 2 replays all 15 affected modules, through `TCSlib` and `audits/pass-shelat/Checks`, at the new head with the logging runner; every row's `source_sha256` equals the committed blob at that head (`evidence-r2/replay.jsonl`, cross-checked against `source-head-r2.json`). The seal probe and axiom prints were rerun at the same head. |
| G12-02 | minor | **Fixed.** Both modules now cite the single-to-many hybrid argument at [PS10, p. 103] (and [Pas09, Theorem 2]) and state that the adaptive extension is added here; Algorithm 104.3 / Theorem 104.4 are kept only as the single-bit construction (book pp. 104–105). Commit `d9fb76a2`. |
| G12-03 | minor | **Fixed (pack).** The round-2 pack says the change introduces exactly two admissions; the replay also reports four existing ones (`OracleSecurity`'s `padded_cpa`, `NonMalleability/Indistinguishability` 1, `NonMalleability/Simulation` 2). |
| note | — | **Applied.** The adaptive sketch's hybrid index needs only `cap(n) > 0`, not `n > 0` (commit `80825587`). |

The two docstring commits change no statement and no code (`evidence-r2/r1-to-r2.diff.txt`).
Round 2 is staged for the same auditor at head `80825587f3d6bda7db2b6472fb0cc88e728e73e7`.
