<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: l2DistSq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Squared L2 distance between two Boolean functions

**Definition.** `l2DistSq f g = expect (fun x => (f x - g x) ^ 2)`, i.e.
`2⁻ⁿ · ∑_x (f(x) - g(x))²` under the uniform measure on the cube
(`expect` and `uniformWeight` from `BooleanAnalysis/Basic.lean`).

It is the *squared* distance — no `Real.sqrt`, unlike `l2Norm` in `Basic.lean` —
so it is the quantity that Parseval evaluates directly: `lowDegree_l2_error`
turns it into a sum of squared Fourier coefficients via `parseval`.

**Remark.** Because it is squared it is not a metric, so no triangle inequality
is available for it. `friedgut_junta` therefore proves the lossy substitute
inline (the `htri` step):
`l2DistSq p r ≤ 2 * l2DistSq p q + 2 * l2DistSq q r`, obtained pointwise from
`sq_nonneg (p x - q x - (q x - r x))` by `nlinarith`. The factor 2 is why the
Friedgut parameters are `ε/4` twice rather than `ε/2`.

**Used in.** `lowDegree_l2_error`, `lowDegree_approx`,
`lowDegreePart_depends_on_influential` and `friedgut_junta` (as the statement's
closeness measure). No call sites outside `BooleanAnalysis/KKL.lean`.
