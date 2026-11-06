# Gate 04 (S2b, #195): round 3 resolutions

- **Round 3:** findings `findings/gate04-s2b-r3-findings.md`, verbatim, SHA-256 `e20d60e517ec8441e7db380769738423b1219962d4d9826c0bb0c3fc26a075f4`; head
  `27ae72da62119ebdde380b8cb2d8c183b59fa2bf`. **0 blockers, 1 major (R3-01), 1 minor (R3-02).**
  R2-01, R2-02, R2-03 and N2 fixed; F02 and N7 not resolved (through R3-01).
- **Ruling (user, 2026-11-06): R-04-4 (A)**, make `Games.QueryImpl` and `Games.OracleSpec.add`
  `abbrev`, so that they are notation under policy §1 (both already have their reading lemmas).
- **Repair:** two commits on #195, `947606fecf1142997661651701f04c3912ba7551` (re-proofs) and
  `a588adfed01eefe6971abd0846e3938ad02e8624` (R-04-4); the full diff is `evidence-r4/repair.diff.txt`.

| Finding | Severity | Resolution |
|---|---|---|
| R3-01 | major | **Fixed.** `ProbComp.expect_bind`'s `pure` case is `simp only [OracleComp.pure_bind, expect_pure]`. The seal is now **complete and automatic**. It covers every one of the 26 Lean files in #195's change set, at the final head. For every declaration, the candidates are collected by a Lean meta program from types, values, transparent foreign instances and the statements of lemmas used in proofs and in `simp`/`rw` lists (`evidence-r4/tool-collect_body.lean.txt`), not hand-picked. A source scan for explicit `unfold`/`rw`/`simp`/`delta` of other files' definitions complements it. The sweep found six more S2a proofs of the same kind in `Games/Protocols.lean` (three `example`s, `Party.stepT_fst`, `closeT_fst`, `execT_outcome`), plus three in `LazySampling.lean` and three in `MultiMessage(Lemmas).lean`; all are re-proved through published equations. 26 of 26 files pass (`seal-evidence.log`), and the `$BASE` control fails exactly at the re-proved declarations (`seal-control-base.log`). The remaining reads are **named exclusions** (`exclusions.md`): section A lists 48 definitional reads and section B 75 explicit unfolds, all in inherited ch. 2–4 declarations that #195 did not change, scheduled for the gate 03 clean-up, part 2 (item J). Section C (type-level reads in `Games/`) is empty after R-04-4. Check: 0 entries on any declaration #195 added or changed. |
| R3-02 | minor | **Fixed.** The change set has **26** Lean files (excluding the root facade); `evidence-r4/changed-files.txt`, and the round 4 pack says so. |
| F02, N7 | (round 1) | **Fixed** through R3-01: the seal covers the whole change set at the final head, with the exclusions named rather than claimed covered. |
