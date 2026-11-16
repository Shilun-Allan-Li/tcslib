# Gate 42 · resolutions, round 1 · HOLD → landing edits

Codex's verdict is **HOLD**: 0 blockers, 1 major, 2 minors, 0 notes.
- **Findings:** `findings/gate42-sc-yao-findings.md`, SHA-256
  `e1076c1e4f643c066106754c0eb02d8d3426b371de47ba698dcecb5504eabdcb`.
- **Audited:** #341 at `e9b03c437aca251846430ff23b40ee5ff3d3347a`; records `f22e0f67`, with the later rulings `67423db6`,
  `d6fe1ddd` and `bf08dbfa`; exchange `747b61e7`.

Codex found **no mathematical gap** in the two frozen targets. It confirmed:
- the efficiency proof, the statistical simulation, the exact endpoints, all five Gate 27 obligations, and the
  quantifier order and total error `δ(n) + 2S(n)|μ(n)|`;
- agreement with the Lindell–Pinkas proof architecture;
- frozen-file integrity, including `Yao.lean`'s six regions plus LE-title and `Uniform.lean`'s seven readers;
- the landing edits LE-bullet, LE-reuse, LE-title and LE-doc;
- Rule 10, the build and the axioms.

SY-F01 to SY-F05 are resolved or accepted under the rulings, with DL-49, DL-51 and DL-52 confirmed against the code.
SY-F06 and SY-F09 are regraded, to G42-01 and G42-03.

| Finding | Grade | Resolution |
|---|---|---|
| G42-01 | **major** | **LE-reuse-2**, proof-only. `RunWithHost.acc_poly` (`RunWithHost.lean:88`) re-proves the public `Complexity.StateLoop.MajLoop.acc_poly` (`Complexity/Randomized/Build/StringLoops.lean:144`) for the same predicate. Its body becomes Codex's candidate: `simpa only [acc_eq, StateLoop.MajLoop.acc_eq] using StateLoop.MajLoop.acc_poly`, or the nearest form that elaborates, reading only the two published readers. There is no import change, since `RunWithHost` already reaches `StringLoops` through `Repetition`. The statement and the helper API are unchanged. No ledger row is needed. |
| G42-02 | minor | **LE-refs**, docstrings only. Full `[AB09]` entry in `ChunkScanner.lean`'s `## References`; full `[BMR90]` entry (Beaver, Micali, Rogaway, "The round complexity of secure protocols", STOC 1990) in `GarblingProgram.lean`'s. |
| G42-03 | minor | **LE-steps**, comments only. Step comments at the major proof boundaries, tied to the existing sketches, in: `yaoHybrid_polyTime` (`Yao.lean:863`, inside an approved body region); `SelectedLaw.acceptProb_fill`; `FakeSimulatorFactory.exists_data`; `SeedCoordinates.pick_iff_place`; `FakeProgram.tables_poly`; `BobIO.outputBit_poly`. Statements and proof terms are unchanged. |

**Checks for the new head:**
- LE-refs and LE-steps are comment-only after stripping comments.
- LE-reuse-2 touches only `acc_poly`'s body.
- The frozen check of `Yao.lean` still passes, with the six regions plus LE-title.
- Built incrementally on the integration tree with the current tip:
  - the changed modules and their downstream give rc 0 with 0 errors;
  - the four Yao results and `yaoProtocol_hbcSecure` use standard axioms only;
  - `RunWithHost`'s canonical coe-A seal passes, and so do its strict and coe B seals.

Then Gate 42 round 2 (Codex) at the new head.
