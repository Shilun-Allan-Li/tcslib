# Isolated native reuse probes: GL probability

DESIGN/STATIC SEARCH ONLY. No Lean/lake/Git command, native probe, source edit, or helper
proof was performed. These are anonymous examples; neither file imports FiniteLinear,
its admitted proposed helper, an implementation of either consumer, or a future theorem.

## Files and context

- MatrixUnitProbabilityExact.lean: full library search in TERM form `exact?%`.
- MatrixUnitProbabilityApply.lean: one tactic block `apply?`, followed only by
  `all_goals sorry` to admit whatever residual goals the search leaves.
- order.txt: root-native module stems matching the existing .lake/io-phfe-probes style.
  Root copies the two files into that isolated directory before running its wrapper.

Both files copy all eight imports currently at the top of live FiniteLinear exactly.
Their only additional root is the already-permitted core Lean.Elab.Tactic.LibrarySearch.
They use the same namespace and Games/Matrix opens as the host. No CoinSampling import,
new generated support module, or additional mathematical import is introduced. The
proposed theorem's exact header is copied as an anonymous example, with natural-count
product cast to Real and denominator q^(n*n), including n=0.

## Why exact?% instead of a second tactic block

AGENTS.md's sorry-ladder rule says never write more than one tactic block per agent
invocation. Core Lean v4.25.0 provides exact?% as the term-form full library search,
so the exact probe needs no tactic block; only the apply probe has one. This is an
existing native API, not a new metaprogram/driver or custom search.

Static source verification:
- Lean/Elab/Tactic/LibrarySearch.lean:57-61 exact? calls exact? requireClose=true.
- The same file:70-85 exact?% calls librarySearch and requires complete closure.
- Lean/Meta/Tactic/LibrarySearch.lean:311-320 default librarySearch uses solveByElim
  with no required terms and maxDepth=6, the same settings used by exact? without using.
The expected failure wording differs: exact?% logs either `didn't find any relevant
lemmas` or `could not close the goal` rather than the tactic's thrown cannot-close.
An incomplete exact term is synthetic-sorry marked and is NOT a proof result.

Core apply? itself admits an incomplete searched main goal after printing its partial
suggestions. The explicit all_goals sorry line merely covers any residual goals; it
does not precede the search, replace the target, or suppress an existing search error.
No `first` fallback, catch, or try tactic hides failure.

## Root's acceptance conditions

Run both files natively through the authorized slot wrapper. Check that each TARGET
TYPE is accepted and that any error is only the expected full-search/no-relevant-lemma
message, not an import, instance, coercion, parser, timeout, or typing failure. Record
complete suggestions separately from partial suggestions containing holes/sorry. Only
a complete proof found by the native search counts as an exact existing match.

Native results are required before authorizing any new helper proof block. These files
make no claim that the target has already typechecked or that the search has failed.
