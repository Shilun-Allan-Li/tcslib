<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The AND-approximating polynomial, by De Morgan

**Definition.** For input polynomials `polys : Fin width → MvPolynomial (Fin vars) (ZMod p)`
and a random seed `S : Fin ℓ → Finset (Fin width)`,

`approxAnd p polys S = 1 - approxOr p (fun i => 1 - polys i) S`.

A plain definition; no proof.

**Reading it.** `approxOr` is the Razborov–Smolensky randomized OR approximator
`1 - ∏ k, (1 - (∑ i ∈ S k, polys i)^(p-1))`. Negating its inputs and its output is
De Morgan, `AND(x) = NOT OR(NOT x)`, which is legitimate here because the `polys`
are only ever evaluated at `0/1` values, where `1 - ·` is Boolean negation. The
definition reuses the same seed `S`, so AND inherits OR's guarantees verbatim:

- `approxAnd_totalDegree` — degree `≤ (p-1) * ℓ * ⨆ i, (polys i).totalDegree`,
  identical to the OR bound;
- `approxAnd_pointwise_bad_count` — for each fixed input, at most a `2^(-ℓ)`
  fraction of seeds is bad. Its proof is entirely bookkeeping: a `Finset.filter`
  congruence showing the AND-bad seeds and the OR-bad seeds are the *same* set
  (each direction by `congrArg (1 - ·)` and `simpa [approxAnd]`), then the OR
  bound.

**Used in.** `approxAnd_totalDegree`, `approxAnd_pointwise_bad_count` and
`exists_good_approxAnd` in this file, and externally in
`RazborovSmolensky/CircuitDegree.lean:440`, where it is the `poly` field of the
`GatePolyFamily` built for the unbounded-AND case of `exists_gate_poly_family`.
