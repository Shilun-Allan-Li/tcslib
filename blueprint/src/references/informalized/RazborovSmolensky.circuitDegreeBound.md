<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: circuitDegreeBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Degree target after `d` layers

**Definition.** For `p ℓ d : ℕ`,

`circuitDegreeBound p ℓ d = ((p - 1) * ℓ) ^ d`.

**Remark.** One layer of approximation multiplies total degree by at most
`(p - 1) * ℓ` (`approxAnd_totalDegree`, `exactMod_totalDegree`), so `d` layers
multiply it by at most the `d`-th power; the recursion
`circuitDegreeBound p ℓ (d+1) = (p - 1) * ℓ * circuitDegreeBound p ℓ d` is exactly
what the `degree` field of `stepLayerFamily` verifies (closed there by
`simp [circuitDegreeBound, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]`). The
arguments are plain naturals — the `p` here shadows the ambient prime and carries
no primality hypothesis of its own.

**Used in.** The `degree` field of `LayerPolyFamily`, and the degree clauses of
`exists_poly_distribution_for_circuit_outputs`, `…_one`, and
`exists_poly_list_for_circuit_one`; downstream in `CircuitSize.lean`,
`SmolenskyAlgebra.lean`, and `RazborovSmolensky.lean`, where it is compared
against `n / 2`.
