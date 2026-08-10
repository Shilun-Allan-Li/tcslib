<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: fourierCoeff_sum_chiS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Uniqueness of the Fourier expansion

**Claim.** For any coefficient family `c : Finset (Fin n) → ℝ` and any frequency
`T : Finset (Fin n)`,
`fourierCoeff (fun x => ∑_{S} c S * chiS S x) T = c T`. Reading off the Fourier
coefficient of an explicit character combination returns the coefficient you put
in. (Here `T` is a *frequency*, not a decision tree, despite the namespace.)

**Proof.** Two steps.

1. A `have expand` computes
   `fourierCoeff (fun x => ∑_S c S * chiS S x) T
   = ∑_S c S * innerProduct (chiS S) (chiS T)`. The `show` unfolds both
   `fourierCoeff` and `innerProduct` into `uniformWeight n * ∑ x …`, and a
   `calc` chain then distributes `chiS T x` into the inner sum
   (`Finset.sum_mul`, `ring`), swaps the order of summation
   (`Finset.sum_comm`), and pushes the `uniformWeight n` factor back inside
   (`Finset.mul_sum`, `← Finset.mul_sum`).
2. Orthonormality of the Walsh characters,
   `BooleanAnalysis.fourier_coeff_chi : innerProduct (chiS S) (chiS T) =
   if S = T then 1 else 0`, gives a `have hterm` rewriting each summand as
   `if S = T then c S else 0` (`split_ifs <;> simp`). Then `simp only [hterm]`
   and a final `simp` collapse the sum to its single surviving term `c T`.

**Used in.** `fourierCoeff_signEval`, and also outside this file: it is the
non-`private` general form, reused in
`TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean` (line 121) to read off the
Fourier coefficients of a restricted function from an explicit expansion,
replacing the textbook's two-stage argument.
