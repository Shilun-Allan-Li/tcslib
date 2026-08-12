<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxAnd_totalDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The AND-approximator obeys the same degree bound as OR

**Claim.** For all `polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)`
and every seed `S : Fin ℓ → Finset (Fin width)`,

`(approxAnd p polys S).totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree`

— the same bound as `approxOr_totalDegree`, again independent of the fan-in
`width`.

**Proof.** `approxAnd` is the De Morgan wrapper
`1 - approxOr p (fun i => 1 - polys i) S`, so after `unfold approxAnd` the outer
subtraction is peeled off by `MvPolynomial.totalDegree_sub` and `max_le`, leaving
two goals:

1. `deg 1 = 0` is below the bound — `simp`.
2. For the `approxOr` part, `approxOr_totalDegree` applied to the complemented
   family gives `(p - 1) * ℓ * ⨆ i, (1 - polys i).totalDegree`. It remains to
   replace that supremum by `⨆ i, (polys i).totalDegree`, which is
   `mul_le_mul_of_nonneg_left (ciSup_mono …)`: boundedness comes from
   `Set.finite_range _ |> Set.Finite.bddAbove`, and the pointwise comparison
   `(1 - polys i).totalDegree ≤ (polys i).totalDegree` is again
   `MvPolynomial.totalDegree_sub` followed by `simp` (`max 0 d = d`).

**Remark.** The one mathematical input is that *complementing an input costs no
degree*: `deg (1 - q) ≤ deg q`. That is what lets the AND approximator inherit the
OR bound verbatim instead of paying an extra factor.

**Used in.** `exists_good_approxAnd`, the unbounded-AND branch of
`exists_poly_for_gate`, and — in
`TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean` — the `degree` field
of the `GatePolyFamily` built by `exists_gate_poly_family`.
