<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitSize.lean :: exists_poly_list_for_circuit_one_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# List form of the single-output distribution, bound stated by circuit size

**Claim.** Under the same hypotheses as
`exists_poly_distribution_for_circuit_one_size` (finite node layers, `Unique out`,
gates in `ACp_GateOps p`), for every `ℓ` there is a list
`Ps : List (MvPolynomial (Fin n) (ZMod p))` with `0 < Ps.length`, every `P ∈ Ps`
satisfying `P.totalDegree ≤ circuitDegreeBound p ℓ F.depth`, and for every Boolean
input `x`,

`(Ps.filter (fun P => P.eval (boolInput x) ≠ F.eval₁ x)).length * 2 ^ ℓ ≤ F.size * Ps.length`.

The list packaging replaces the seed type by explicit multiplicities, so the
"distribution" is a uniform choice from `Ps`.

**Proof.** Three lines.

1. `letI ... Fintype.ofFinite` for the node layers.
2. `rcases exists_poly_list_for_circuit_one` supplies `Ps`, positivity, and the
   degree bound; `refine` forwards them.
3. `simpa [gateCountBefore_depth_eq_size]` rewrites `gateCountBefore F F.depth` as
   `F.size` in the inherited error bound.

**Remark.** A restatement wrapper; the list-vs-finset translation itself happens
upstream in `exists_poly_list_for_circuit_one`.
