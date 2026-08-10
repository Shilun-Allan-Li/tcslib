<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: orthProj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Projection off a unit vector

**Definition.** For a real inner-product space `V` and `u v : V`,

```
orthProj u v = v - (inner ℝ u v) • u
```

the component of `v` orthogonal to `u`.

**Remark.** The definition carries no hypothesis on `u`; it is the projection
onto `(span ℝ {u})ᗮ` only when `‖u‖ = 1`, and each downstream lemma supplies
that hypothesis explicitly — `orthProj_mem_orthogonal` (membership in the
orthogonal complement), `orthProj_ne_zero` (nonvanishing when `v ≠ ±u`),
`orthProj_inner_nonpos` (nonpositive inner products are preserved).

**Used in.** The dimension-reduction step of `rankin_bound_general`: unit
vectors with pairwise nonpositive inner products are pushed into the
`(n-1)`-dimensional space `(span ℝ {u})ᗮ` as `‖orthProj u v‖⁻¹ • orthProj u v`
(see `mkProj`, `norm_normalized_orthProj`, `normalized_orthProj_injective`,
`normalized_orthProj_inner_nonpos`), which drives the induction behind
`rankin_finset_bound` and ultimately `binary_johnson_card_bound`.
