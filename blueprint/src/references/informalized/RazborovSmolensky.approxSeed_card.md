<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxSeed_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The number of random seeds

**Claim.** `Fintype.card (Fin ℓ → Finset (Fin width)) = 2 ^ (width * ℓ)`.

A seed for the approximator is a choice of `ℓ` subsets of the `width` input wires,
so there are `(2 ^ width) ^ ℓ = 2 ^ (width · ℓ)` of them.

**Proof.** A three-step `calc`:

1. `Fintype.card (Fin ℓ → Finset (Fin width)) = (Fintype.card (Finset (Fin width))) ^ ℓ`
   by `simp` (`Fintype.card_fun` with `Fintype.card_fin`).
2. `= (2 ^ width) ^ ℓ` by `simp` — the power set of an `n`-element type has `2 ^ n`
   elements.
3. `= 2 ^ (width * ℓ)` by `rw [← Nat.pow_mul]`.

**Used in.** The length computations `approxOrPolyList_length` and
`approxAndPolyList_length`, the counting bound `approxOr_pointwise_bad_count`, the
AND branch of `exists_poly_for_gate`, and — in
`TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean` —
`exists_gate_poly_family`.
