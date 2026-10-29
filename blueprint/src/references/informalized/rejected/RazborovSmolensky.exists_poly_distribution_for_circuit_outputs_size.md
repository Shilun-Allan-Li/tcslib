<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitSize.lean :: exists_poly_distribution_for_circuit_outputs_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Simultaneous polynomial distribution for all outputs, bound stated by circuit size

**Claim.** Let `F : FeedForward (Fin 2) (Fin n) out` have finite node layers and
finite output type, and let all its gates lie in `ACp_GateOps p`. For every `ℓ`
there is a finite seed type `Seed` with decidable equality, `0 < Fintype.card Seed`,
and `P : Seed → out → MvPolynomial (Fin n) (ZMod p)` such that every
`(P s o).totalDegree ≤ circuitDegreeBound p ℓ F.depth`, and for every Boolean input
`x`,

`#{s | ∃ o, (P s o).eval (boolInput x) ≠ F.eval x o} * 2 ^ ℓ ≤ F.size * Fintype.card Seed`.

Same content as `exists_poly_distribution_for_circuit_outputs`, with
`gateCountBefore F F.depth` replaced by `F.size`.

**Proof.** Three lines.

1. `letI` upgrades the `Finite (F.nodes i)` instances to `Fintype` via
   `Fintype.ofFinite`.
2. `rcases exists_poly_distribution_for_circuit_outputs` supplies
   `Seed, instF, instD, P` and the three properties; `refine` re-packages them,
   leaving only the error bound.
3. `simpa [gateCountBefore_depth_eq_size]` rewrites `gateCountBefore F F.depth` to
   `F.size` in `hbad x`.

**Remark.** A restatement wrapper, not a new argument; the work is in
`buildLayerFamily`/`stepLayerFamily` upstream.
