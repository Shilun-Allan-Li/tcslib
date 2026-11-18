# Algebra oneSd matrix overlap V2 — UNRUN

The same literal factor lambdas are wrapped with the existing public Matrix.of.
No entry, dimension, hypothesis, multiplication or conclusion changes. Imports are
unchanged and include no owned source; static full import closure has no Obfuscation.
Unused BigOperators scope is removed. One marker and zero tactic blocks per template.
The copied original materializer was not invoked; root owns fresh exact?/apply? runs.

Root cause is not a missing Matrix scope. Matrix HMul is an ordinary global instance
in Mathlib/Data/Matrix/Mul.lean:288-291. That same module's documentation:40-43 warns
that literal functions, even with a Matrix type annotation, may not be recognized as
matrices for multiplication and recommends Matrix.of. Its existing definition in
Mathlib/LinearAlgebra/Matrix/Defs.lean:69-80 is the identity equivalence, used exactly
for this typeclass distinction. No new helper/definition/import/axiom is introduced.

bindings.json and unified diffs preserve the original template byte bindings.
The former6 runs (4full SparseFactor goals +2generic oneSd core) failed HMul before
search; superseded-runs.json marks them as harness failures, not negative overlap
results. This is based on root's report; this agent did not run or reclassify logs.
All V2 results remain pending root; no Lean/materializer/source/git/cache/spawn.

This packet contains only oneSd_factors_mul; root driver label AlgebraMatrixV2
should map here. Other scope-fixed AlgebraV2 mappings may continue using old packet.
