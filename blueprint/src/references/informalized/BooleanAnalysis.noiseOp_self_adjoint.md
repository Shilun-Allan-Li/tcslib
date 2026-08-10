<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: noiseOp_self_adjoint -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.68) -->

# The noise operator is self-adjoint

**Claim.** For any noise rate `ρ : ℝ` and any `f g : BooleanFunc n`,
`innerProduct (noiseOp ρ f) g = innerProduct f (noiseOp ρ g)`. So `T_ρ` may be
moved from either side of the inner product to the other.

**Proof.** A `calc` chain in the Fourier domain.

1. `plancherel` rewrites the left inner product as
   `∑ S, fourierCoeff (noiseOp ρ f) S * fourierCoeff g S`.
2. Termwise (`Finset.sum_congr rfl`), `noiseOp_fourier` replaces each
   `fourierCoeff (noiseOp ρ f) S` by `ρ ^ S.card * fourierCoeff f S`.
3. Termwise `ring` reassociates `(ρ^|S| * f̂(S)) * ĝ(S)` into
   `f̂(S) * (ρ^|S| * ĝ(S))` — the only actual content of the proof.
4. `noiseOp_fourier` again, read right-to-left, folds `ρ^|S| * ĝ(S)` back into
   `fourierCoeff (noiseOp ρ g) S`.
5. `← plancherel` turns the sum back into `innerProduct f (noiseOp ρ g)`. ∎

**Remark.** Self-adjointness is exactly the commutativity of real
multiplication once `T_ρ` is diagonalised in the Walsh basis; it is what lets
`stability_formula` write the noise stability `⟪f, T_ρ f⟫` symmetrically as
`∑_S ρ^{|S|} f̂(S)²`.
