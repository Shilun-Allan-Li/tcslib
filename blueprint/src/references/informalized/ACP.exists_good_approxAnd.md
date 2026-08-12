<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: exists_good_approxAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A list of low-degree AND-approximators, good on average at every point

**Claim.** The AND-analogue of `exists_good_approxOr`. For any
`polys : Fin width → MvPolynomial (Fin vars) (ZMod p)` there is a list `Ps` with

- `Ps = approxAndPolyList p polys`,
- `Ps.length = 2 ^ (width * ℓ)`,
- `P.totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree` for every `P ∈ Ps`, and
- for every `y`, the number of seeds `S` with
  `(approxAnd p polys S).eval y ≠ ∏ k, (1 - (1 - (polys k).eval y) ^ (p - 1))`, times
  `2 ^ ℓ`, is at most `Ps.length`.

**Proof.** Same four-goal `refine` as the OR version, with the AND lemmas substituted.

1. `rfl` for the defining equation; `approxAndPolyList_length` for the length.
2. Degree: `List.mem_map.mp` extracts the seed, then `approxAnd_totalDegree`.
3. Pointwise count: `approxAnd_pointwise_bad_count`, followed by
   `(approxAndPolyList_length …).symm` inside a `calc` to turn `2 ^ (width * ℓ)` back into
   `Ps.length`.

**Remark.** The target on the right of the `≠` is the exact AND indicator
`∏ k, (1 - (1 - (polys k).eval y) ^ (p - 1))`, i.e. the De Morgan dual of the OR target;
`exactAnd_on_bits` is what later identifies it with a genuine Boolean AND.

**Status.** No Lean consumers at present — blueprint-facing
(`ACP.exists_good_approxAnd`); the AND branch of `exists_poly_for_gate` and of
`RazborovSmolensky/CircuitDegree.lean` use `approxAnd_pointwise_bad_count` directly.
