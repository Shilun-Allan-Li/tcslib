<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: noisyInfluence_le_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Noisy influence is at most the ordinary influence

**Claim.** For `0 ≤ ρ ≤ 1`, `noisyInfluence ρ i f ≤ influence i f`.

**Proof.** After `noisyInfluence` and `influence_eq_sum_fourier`, both sides are
sums over `S : Finset (Fin n)` of guarded terms, so `Finset.sum_le_sum` reduces
to a termwise comparison:

- `i ∈ S`: goal `ρ ^ (S.card - 1) * f̂(S)² ≤ f̂(S)²`, closed by
  `mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hρ0 hρ1)` — the noise factor
  is a power of a number in `[0,1]`, hence at most 1.
- `i ∉ S`: both terms are `0`, `le_refl`. ∎

**Note.** This is the trivial monotonicity bound, and it is the *only* bound on
noisy influence the file has. `noisyInfluence_power_bound`, which is stated as if
it gave the log-convexity estimate `Inf_i^ρ[f] ≤ (Inf_i[f])^ρ`, in fact just
delegates to this lemma (`exact noisyInfluence_le_influence i f ρ …`). That gap
is why the hard case of `KKL_balanced` is left as **`sorry`** (KKL.lean:618): the
`log n / (30n)` bound needs the genuine log-convexity, and the trivial bound is
too weak to supply it.
