<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: exists_good_approxOr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A list of low-degree OR-approximators, good on average at every point

**Claim.** For any `polys : Fin width → MvPolynomial (Fin vars) (ZMod p)` there is a list
`Ps` of polynomials such that

- `Ps = approxOrPolyList p polys` (the canonical seed-indexed list),
- `Ps.length = 2 ^ (width * ℓ)`,
- every `P ∈ Ps` has `P.totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree`, and
- for every `y : Fin vars → ZMod p`, the number of seeds `S` with
  `(approxOr p polys S).eval y ≠ 1 - ∏ k, (1 - ((polys k).eval y) ^ (p - 1))`, times
  `2 ^ ℓ`, is at most `Ps.length`.

**Proof.** `refine` the canonical witness and discharge four goals.

1. The equation is `rfl` by construction.
2. The length is `approxOrPolyList_length`.
3. Degree: for `P ∈ Ps`, `List.mem_map.mp` produces the seed `S` with `P = approxOr p polys S`,
   and `approxOr_totalDegree` gives the bound.
4. Pointwise failure count: `approxOr_pointwise_bad_count` bounds it by `2 ^ (width * ℓ)`,
   which is `Ps.length` by `approxOrPolyList_length` (used in the `symm` direction inside a
   `calc`).

**Remark.** Purely a repackaging step: it bundles the degree bound and the pointwise
bad-seed bound into one existential over an explicit list, so that a caller never has to
mention the seed type. The list (rather than a set) keeps multiplicities, which is what
makes "at most a `2^{-ℓ}` fraction of entries" a statement about `Ps.length`.

**Status.** No Lean consumers at present — it is a blueprint-facing statement
(`ACP.exists_good_approxOr` in `blueprint/.../ACpGates.tex`); the circuit-level argument in
`RazborovSmolensky/CircuitDegree.lean` uses the seed-indexed form instead.
