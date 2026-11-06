# Open questions for the user (morning of 2026-11-07)

**Q1 and Q2 answered 2026-11-07** (decision log): Q1 (A), Q2 (A) with a standing rule for fill-owned files.

## Q1. How should statement-level reads of `PolyExpr.eval` be fixed? (blocks: gate 07 round 2, the eval-dependent part of #195's zero-exclusion repair)

The complete sweep (`gates/07-eqlemmas/sweep/REPORT.md`) found 59 statement reads and 26
definition-body reads whose minimal foreign set contains `Complexity.PolyExpr.eval`
(`Complexity/Randomized/PolyExpr.lean`, this campaign's file, not `main`'s). They are typed lengths:
a value of type `Fin ((.add p q).eval n) → Bool` used where `Fin (p.eval n + q.eval n) → Bool`
(or `Fin (m + m)`, `Fin n`) is expected, so the statement elaborates only because `eval` computes.
This includes the three PRF statements of R-04-5 (A), the `FunFamily.glPad` reads of gate 07 F01,
and the `PermFamily.toFunFamily` headline statements (`owp_hardcore_prg`, `owp_commitment`,
`zk_proof_of_owp_levinReduction`, …).

Options:
- **(A) Treat `eval` as notation** (recommended by the sweep): make `PolyExpr.eval` reducible
  (`@[reducible]`, or an `abbrev`-style definition by structural recursion), extending ruling
  R-04-4's principle (definitions that only compute types are notation under policy §1). No
  statement changes for these reads; the remaining reads (`glPad`, `toFunFamily`) are then fixed
  by published equivalences. Risk: elaboration may unfold `eval` more eagerly (performance); the
  replay would show it.
- **(B) Published transports per constructor:** `Fin`-equivalences for `eval` on `const`/`var`/
  `add`/`mul`/`pow` (and `normal`), and every one of the 85 consumers restated through them. Fully
  within the current policy; large, and the restated statements carry casts.
- **(C) Hybrid:** (A) for `eval` on constructors only through a few `@[reducible]` wrapper
  definitions (`PolyExpr.var.eval` etc. as lemmas cannot do this), else (B). Probably not simpler.

Meanwhile all reads that do not involve `eval` are being fixed (#210 follow-up; #195 stacked
repair), and the fills are issued on #210's head (no fill target is among the reads).

## Q2. File sizes: `Asymptotic/PublicKey.lean` (1038 lines after #210, was 989) and `Candidates/DiscreteLog.lean` (1426 after the dl-a fill, was 973)

Options: (A) a size exception, like RSA, Rabin, Collections and `ThreeColoring/Protocol.lean`;
(B) move the self-contained Lem-104.a block (`pkPredictor`, `predProb_pkPredictor_*`,
`exists_pkPredictor`, about 70 lines) into `PublicKeyLemmas.lean` (which then imports
`Asymptotic/HardCore` and `Pseudorandom/GeneratorFromPermutation`). It blocks only gate 07 round 2's
lint line, not the fills.
`Candidates/DiscreteLog.lean`: the dl-a fill (all 7 targets filled) takes it from 973 to 1426
lines. Options: (A) a size exception, as for the other fill-owned files; (B) a split as a landing
edit (the fill's new private helpers into a `DiscreteLogSampler.lean` helper module imported by
`DiscreteLog.lean`). Later fills will raise the same question for other owned files.
