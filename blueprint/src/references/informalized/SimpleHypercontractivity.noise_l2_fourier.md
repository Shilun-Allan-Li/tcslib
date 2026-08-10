<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: noise_l2_fourier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The L² norm of T_ρ f in Fourier space

**Claim.** For `ρ : ℝ` and `f : BooleanFunc n`,

`innerProduct (noiseOp ρ f) (noiseOp ρ f) = ∑ S : Finset (Fin n), (ρ ^ S.card) ^ 2 * fourierCoeff f S ^ 2`.

That is, `𝔼[(T_ρ f)²] = ∑_S ρ^{2|S|} f̂(S)²`.

**Proof.**

1. `parseval` rewrites the self inner product as
   `∑ S, fourierCoeff (noiseOp ρ f) S ^ 2`.
2. Termwise (`Finset.sum_congr rfl`), `noiseOp_fourier` replaces
   `fourierCoeff (noiseOp ρ f) S` by `ρ ^ S.card * fourierCoeff f S`.
3. `ring` squares the product into `(ρ ^ S.card) ^ 2 * fourierCoeff f S ^ 2`. ∎

**Used in.** `contractivity`, where each factor `(ρ^{|S|})² = (ρ²)^{|S|} ≤ 1` is
dropped to give `𝔼[(T_ρ f)²] ≤ 𝔼[f²]` whenever `ρ² ≤ 1`.
