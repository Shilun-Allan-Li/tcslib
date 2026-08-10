<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: noiseOp_compose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Composing noise operators multiplies their parameters

**Claim.** For `ρ σ : ℝ` and `f : BooleanFunc n`,
`noiseOp ρ (noiseOp σ f) = noiseOp (ρ * σ) f`. So the operators `T_ρ` form a
one-parameter semigroup: `T_ρ ∘ T_σ = T_{ρσ}`. Note this is an equality of
functions, with no sign or size hypothesis on `ρ`, `σ`.

**Proof.**

1. `ext x` and `simp only [noiseOp]` reduce to equality of the two Fourier sums
   `∑ S, ρ^{|S|} · (T_σ f)̂(S) · χ_S x` and `∑ S, (ρσ)^{|S|} · f̂(S) · χ_S x`.
2. `congr 1; ext S` moves to a single frequency, where `noiseOp_fourier`
   rewrites `(T_σ f)̂(S)` as `σ^{|S|} · f̂(S)`.
3. `ring` finishes: `ρ^{|S|} · σ^{|S|} = (ρσ)^{|S|}`. ∎

**Remark.** The content is just `mul_pow` in the Walsh basis, where `T_ρ` is
diagonal. It is used in `Hypercontractivity/General.lean` to split a noise rate
into two stages, e.g. rewriting `T_ρ` as `T_{ρ/ρ₀} ∘ T_{ρ₀}`.
