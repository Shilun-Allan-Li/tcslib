<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitSize.lean :: exists_poly_distribution_for_circuit_one_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Single-output polynomial distribution, bound stated by circuit size

**Claim.** Let `F : FeedForward (Fin 2) (Fin n) out` have finite node layers, a
`Unique` output type, and gates only from `ACp_GateOps p`. For every `ℓ` there is a
finite seed type `Seed` with decidable equality, `0 < Fintype.card Seed`, and
`P : Seed → MvPolynomial (Fin n) (ZMod p)` with each
`(P s).totalDegree ≤ circuitDegreeBound p ℓ F.depth`, such that for every Boolean
input `x`,

`#{s | (P s).eval (boolInput x) ≠ F.eval₁ x} * 2 ^ ℓ ≤ F.size * Fintype.card Seed`.

**Proof.** Three lines.

1. `letI ... Fintype.ofFinite` produces `Fintype` instances for the node layers.
2. `rcases exists_poly_distribution_for_circuit_one` gives the seed type,
   instances, family, positivity and degree bound; `refine` forwards all but the
   error bound.
3. `simpa [gateCountBefore_depth_eq_size]` converts the inherited bound's
   `gateCountBefore F F.depth` into `F.size`.

**Remark.** A restatement wrapper over
`exists_poly_distribution_for_circuit_one`; no new mathematics.
