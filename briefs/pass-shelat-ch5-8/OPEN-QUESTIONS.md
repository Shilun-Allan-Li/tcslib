# Open questions for the user (morning of 2026-11-07)

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
