<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: approxAnd_pointwise_bad_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# At most a `2^{-ℓ}` fraction of seeds are bad for AND at a fixed input

**Claim.** For every `polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)`
and every point `y : Fin vars → ZMod p`,

`#{S : Fin ℓ → Finset (Fin width) | (approxAnd p polys S).eval y ≠ ∏ k, (1 - (1 - (polys k).eval y) ^ (p - 1))} * 2 ^ ℓ ≤ 2 ^ (width * ℓ)`.

The right-hand product is the *exact* AND of the inputs at `y`: each factor
`1 - (1 - x) ^ (p - 1)` is the Fermat indicator of `x = 1`, so the product is `1`
exactly when every input is `1`. As with OR, the bad-seed fraction is at most
`2 ^ (-ℓ)`.

**Proof.** Transport of `approxOr_pointwise_bad_count` across De Morgan.

1. Instantiate `h := approxOr_pointwise_bad_count (p := p) vars width ℓ
   (fun i => 1 - polys i) y` — the OR bound for the complemented family.
2. Show the two bad-seed filters are *equal* (`hfilter`), namely that
   `(approxAnd p polys S).eval y ≠ ∏ k, …` iff
   `(approxOr p (fun i ↦ 1 - polys i) S).eval y ≠ 1 - ∏ k, (1 - ((1 - polys k).eval y) ^ (p - 1))`.
   After `ext S` and `simp only [Finset.mem_filter, Finset.mem_univ, true_and]`,
   each direction is a `by_contra`: from the *good* case of one form, applying
   `congrArg (fun z : ZMod p => 1 - z)` and `simpa [approxAnd]` produces the good
   case of the other, contradicting the assumed badness. The step works because
   `1 - (1 - z) = z` in `ZMod p` and because `MvPolynomial.eval` is a ring
   homomorphism, so `(1 - polys k).eval y = 1 - (polys k).eval y`.
3. `rw [hfilter]; exact h`.

**Remark.** Since the filters are literally equal — not merely equinumerous — no
counting is redone here; the `2 ^ ℓ` saving is inherited unchanged from the OR
case, which in turn rests on `count_bad_S` and `subset_sum_zero_bound`.

**Used in.** `exists_good_approxAnd`, the unbounded-AND branch of
`exists_poly_for_gate`, and — in
`TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean` — the `bad` field of
the `GatePolyFamily` built by `exists_gate_poly_family`.
