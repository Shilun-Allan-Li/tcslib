<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: sum_noisyInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Summing the noisy influences over all coordinates

**Claim.** For any noise rate `ρ : ℝ` and `f : BooleanFunc n`,

`∑ i, noisyInfluence ρ i f = ∑ S, S.card * ρ ^ (S.card - 1) * fourierCoeff f S ^ 2`.

Each `noisyInfluence ρ i f` is `∑_{S ∋ i} ρ^(|S|-1) f̂(S)²`, so summing over `i`
counts every `S` once per element of `S` — which is what puts the factor `|S|` on
the right.

**Proof.** Exchange the two sums, then collapse the inner one.

1. `simp only [noisyInfluence]` exposes the double sum, and `Finset.sum_comm` puts
   the sum over frequencies `S` outside.
2. Fix `S`. The inner summand is `if i ∈ S then ρ^(|S|-1) * f̂(S)² else 0`, so
   `← Finset.sum_filter` restricts it to `i ∈ S`, and
   `Finset.filter_mem_eq_inter` with `Finset.univ_inter` identifies that filter
   with `S` itself.
3. The summand no longer mentions `i`, so `Finset.sum_const` and `nsmul_eq_mul`
   turn the inner sum into `S.card * (ρ^(|S|-1) * f̂(S)²)`; `ring` matches the
   associativity of the target.

**Remark.** The exponent `S.card - 1` is truncated ℕ subtraction, so for `S = ∅`
it reads `ρ^0 = 1` rather than `ρ^(-1)`; the factor `S.card = 0` deletes that term
anyway, which is why the statement needs no `S ≠ ∅` side condition.

**Used in.** Step B of `KKL_balanced` (the only reference, in the same file),
where it rewrites the noisy total influence at rate `ρ^2` into a Fourier sum.
