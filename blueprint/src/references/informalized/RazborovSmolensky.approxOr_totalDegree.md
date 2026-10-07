<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxOr_totalDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The OR-approximator multiplies degree by at most `(p-1)ℓ`

**Claim.** For all `polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)`
and every seed `S : Fin ℓ → Finset (Fin width)`,

`(approxOr p polys S).totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree`.

The bound is *independent of the fan-in* `width` — this is the whole point of the
approximation, and the source of the degree bound for `AC⁰[p]` circuits.

**Proof.** Two steps: bound one factor, then sum over the `ℓ` factors.

1. **One factor** (`h_term k`): for each `k`,
   `(1 - (∑ i ∈ S k, polys i) ^ (p - 1)).totalDegree ≤ (p - 1) * ⨆ i, (polys i).totalDegree`.
   `grw [MvPolynomial.totalDegree_sub]` replaces the difference by
   `max (deg 1) (deg (…))`, and `simp only [MvPolynomial.totalDegree_one, zero_le,
   sup_of_le_right]` discards the `deg 1 = 0` branch. Then
   `grw [MvPolynomial.totalDegree_pow]` extracts the factor `p - 1`, and
   `mul_le_mul_of_nonneg_left` reduces the goal to
   `(∑ i ∈ S k, polys i).totalDegree ≤ ⨆ i, (polys i).totalDegree`. Finally
   `grw [MvPolynomial.totalDegree_finsetSum_le]` bounds the subset sum by the
   supremum of its summands' degrees, and each summand is handled by
   `le_ciSup`, whose boundedness side condition comes from
   `Set.finite_range … |> Set.Finite.bddAbove` (the index type `Fin width` is
   finite, so the range of degrees is bounded above).

2. **Over all factors:** `trans ∑ k, (1 - (∑ i ∈ S k, polys i) ^ (p - 1)).totalDegree`.
   The first leg unfolds `approxOr` and applies
   `MvPolynomial.totalDegree_sub` together with
   `MvPolynomial.totalDegree_finset_prod` — the degree of a product is at most
   the sum of the degrees — closed by `simp`. The second leg is
   `Finset.sum_le_sum fun i _ ↦ h_term i`, giving
   `ℓ * ((p - 1) * ⨆ i, (polys i).totalDegree)`, which
   `simp [mul_assoc, mul_comm]` reassociates into the stated
   `(p - 1) * ℓ * ⨆ i, (polys i).totalDegree`.

**Remark.** The `⨆` is a `ciSup` over `i : Fin width` in `ℕ`; boundedness is
supplied by finiteness of the range at each use, and for `width = 0` it degenerates
to `0`.

**Used in.** `exists_good_approxOr` (the degree clause of the list) and
`approxAnd_totalDegree`, which transports this bound across De Morgan.
