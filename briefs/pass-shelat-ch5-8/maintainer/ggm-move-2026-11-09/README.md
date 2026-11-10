# Asymptotic GGM relocation

Seyoon merged the oracle and PRF contract move #268 at `7e3a4b21e835cfc951000015a1f049f82a654abb`. Its Lean
sources and checker inputs match the verified head `77e0232adeefdb0c7cf0abec14da6925bd8e1bcf`.

[PR #269](https://github.com/Shilun-Allan-Li/tcslib/pull/269) at `39e3a1b167aabe26151f2906e1505d32b8c79dfa` puts the construction, security proof and
PRG-to-PRF existence theorem in `Pseudorandom.Functions.Asymptotic.GGM`.
`GGM.Evaluator` owns the tree walk. `GGM.Reduction` owns the lazy table,
lookup loop, reduction components and time bound. `GGM.Run` packages the
machine and proves its agreement with the finite distinguisher.

The new route imports shared reduction support and the finite GGM development.
The import graph is independent of the hard-core construction. The legacy
`Asymptotic.PRF`, `PRFLemmas`, `GGMReduction` and `GGMReductionEval` paths
re-export the moved results and preserve their prior import closures.

- All 30 affected modules pass from source, including the library root and
  campaign Checks. The replay verifies 1,069 transferred local objects and
  3,810 external objects.
- All 378 declaration types, definition values and axiom sets match. The
  comparison normalizes 11 relocated private names and generated binder
  scopes. The declaration and proof text moves verbatim, with an updated
  documentation link for the history encoding. The legacy and standalone
  import probes agree.
- The whole-file seals map all 13 diagnostics to the same baseline proof steps.
  The control blocks direct reduction of `GGMRed.histEnc` and accepts its
  published equation. The explicit scan has zero hits. The two generated
  references and 34 deferred provider links map to the new locations.
  [Ledger mapping](READS.json)
- The source linter's one size finding follows the reduction file. It is 1,103
  lines after relocation, down from 1,104. Its lazy table representation, guarded
  state loop and time proof share one proof file and retain that boundary.
  The campaign lint adds no facade findings or reader warnings.

`ggm-checks.zip` has SHA-256 `e8e59d09a78e875c79092a5a60c4a3b1897f9bd1cb47437a485f2c6ba5e02ca9`.
[Verification hashes](VERIFICATION.json)

Seyoon merged #269 at `88befb0df9c2cd295dfc5d6d5a5e861ea4024314`. The Lean sources and checker inputs match the verified head.
