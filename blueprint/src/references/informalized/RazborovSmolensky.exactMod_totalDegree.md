<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: exactMod_totalDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `exactMod` multiplies degree by at most `p - 1`

**Claim.** For any `polys : Fin width → MvPolynomial (Fin vars) (ZMod p)`,

`(exactMod p polys).totalDegree ≤ (p - 1) * ⨆ i, (polys i).totalDegree`.

**Proof.** A four-step degree computation on `1 - (∑ i, polys i) ^ (p - 1)`, all by
`grw` rewriting with the standard `MvPolynomial` degree bounds.

1. `MvPolynomial.totalDegree_sub` bounds the difference by the max of the two degrees;
   `MvPolynomial.totalDegree_one` makes the `1` side `0`, so `sup_of_le_right` discards it.
2. `MvPolynomial.totalDegree_pow` gives `(p - 1) * (∑ i, polys i).totalDegree`.
3. `mul_le_mul_of_nonneg_left` reduces to bounding `(∑ i, polys i).totalDegree` by the
   supremum, and `MvPolynomial.totalDegree_finsetSum_le` reduces that to the individual
   summands.
4. `le_ciSup` finishes, its `BddAbove` side condition supplied by
   `Set.finite_range … |>.bddAbove` (the index type `Fin width` is finite).

**Remark.** The `⨆` is a conditionally-complete-lattice supremum over `ℕ`, hence the need
for the explicit boundedness witness. The proof is the same skeleton as the inner
`h_term` step of `approxOr_totalDegree`, minus the product over the `ℓ` seeds.

**Used in.** The degree obligation of the `MOD` branch of `exists_poly_for_gate`, and in
`RazborovSmolensky/CircuitDegree.lean:480`.
