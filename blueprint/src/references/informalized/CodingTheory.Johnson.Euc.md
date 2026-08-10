<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: Euc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `Euc n`: the ambient Euclidean space

**Definition.** `Euc n` is the abbreviation `EuclideanSpace ℝ (Fin n)`, i.e.
`ℝ^n` with the standard real inner product `⟪·,·⟫_[ℝ]`, coming from Mathlib's
`WithLp 2` structure on `Fin n → ℝ`. It is where the geometric side of the
Johnson argument takes place: `pmOne`, `ones`, `shifted` and `normalize` all land
in `Euc n`, and `rankin_finset_bound` bounds finite sets of unit vectors in it.

**Remark.** Being an `abbrev`, it unfolds to `EuclideanSpace ℝ (Fin n)` and so
inherits `NormedAddCommGroup`, `InnerProductSpace ℝ` and `FiniteDimensional ℝ`
with `Module.finrank ℝ (Euc n) = n` — this is what lets the specialised
`rankin_finset_bound` be obtained from the general
`rankin_bound_general` with the `2 * finrank` bound read as `2 * n`. Vectors are
built with `WithLp.toLp 2` and coordinates are extracted by ordinary function
application, so `RCLike.wInner` unfolds inner products to sums over `Finset.univ`.
