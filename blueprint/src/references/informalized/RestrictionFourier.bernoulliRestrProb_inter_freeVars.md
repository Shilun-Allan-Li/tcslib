<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: bernoulliRestrProb_inter_freeVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The probability that `U` meets the free set exactly in `S`

**Claim.** For `p : ℝ` and finsets `U S : Finset (Fin n)`, under a
Bernoulli(`p`)-random restriction `ρ` with free set `J = ρ.freeVars`,

`bernoulliRestrProb p (fun ρ => U ∩ ρ.freeVars = S)`
` = if S ⊆ U then p ^ S.card * (1 - p) ^ (U \ S).card else 0`.

**Proof.** Apply the squared-coefficient identity to the character `f = χ_U`.

1. `hLHS`: for every `ρ`,
   `fourierCoeff (restrictBF (chiS U) ρ) S ^ 2 = if U ∩ ρ.freeVars = S then 1 else 0`.
   Expand by `fourierCoeff_restrictBF`; `fourier_coeff_chi` says
   `fourierCoeff (chiS U) U' = if U = U' then 1 else 0`, so `Finset.sum_ite_eq`
   collapses the sum over `U'` to the single term `U' = U`. In the surviving
   branch `signProd_sq` gives `1`; otherwise `zero_pow` gives `0`.
2. `key := expectation_fourierCoeff_sq_restrictBF p (chiS U) S`, with `hLHS`
   rewritten into its left-hand side. That left-hand side is now literally the
   definition of `bernoulliRestrProb p (fun ρ => U ∩ ρ.freeVars = S)`, so
   `unfold bernoulliRestrProb; rw [key]`.
3. `hRHS`: the same `fourier_coeff_chi` collapse on the right-hand sum (again via
   `Finset.sum_ite_eq`) leaves only `U' = U`, yielding the stated
   `if S ⊆ U then p ^ |S| * (1 - p) ^ |U \ S| else 0`.

**Remark.** This is O'Donnell's probability form of Proposition 4.17: read
together with `expectation_fourierCoeff_sq_restrictBF` it says
`E_ρ[f̂_ρ(S)²] = ∑_U Pr[U ∩ J = S] · f̂(U)²`. Note the statement holds for any
real `p`, with no `0 ≤ p ≤ 1` hypothesis — the "probability" reading requires
the caller to supply that.
