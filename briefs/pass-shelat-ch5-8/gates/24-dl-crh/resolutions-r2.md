# Gate 24 · resolutions, round 2 · CLOSED

Codex's verdict is **CLEAR**: 0 blockers, 0 majors, 0 minors and 0 notes. All three round-1 findings are closed.

- **Findings:** `findings-r2/gate24-dl-crh-r2-findings.md`.
- **Audited head:** `d356381aadc350860f9a0e97123e84d9aefa585b`.
- **Pins:** records `a518558d26988753261c73b436c4493adbc16cb0`, exchange `9bdc6e341003529631f2b5b2d61c5399deba0969`.

| # | Round 1 | Round 2 |
|---|---|---|
| G24-01 | major | **Closed by LE-reuse.** `inputWord_take` reads `take_ofFn_castLE` and `inputWord_split` reads `ofFn_eq_init_append`. Statements and docstrings are unchanged, and the new import is acyclic. The expanded seals and controls pass. |
| G24-02 | minor | **Closed by the erratum.** The example needs `z = 0`, as the round-2 pack disclosed. |
| G24-03 | minor | **Closed by the erratum** in `resolutions-r1.md`. |

**What Codex checked independently, without running Lean:**
- **The one new commit:** it reproduced it from the round-1 bytes.
- **Headers:** all 197 are unchanged.
- **The 128-file closure:** it matches the pinned sources.
- **Seal request sets:** each gains exactly 24 rows, from the four imported modules.
- **Carrying the other files' round-1 seals forward:** justified, because their sources and oleans are unchanged.
- **Merge trees:** it reconstructed both trial-merge trees, and the merge onto `47e6cf47`, which is tree `b8b1308a` and Lean-identical to the second trial. That trial covers #307 with #303, #306, #308 and #309.
- **Integration:** no name clashes, standard axioms only, and lint 92 FAIL / 101 WARN at the merges with no added FAIL.

## Disposition
No change is needed. **PR [#307](https://github.com/Shilun-Allan-Li/tcslib/pull/307) is marked ready at `d356381a`.**
Its merge onto the current tip is conflict-free and was built in the second trial. DL-41's remaining items stay
deferred with the cleanup.
