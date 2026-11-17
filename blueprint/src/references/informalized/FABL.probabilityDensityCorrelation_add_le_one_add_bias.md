<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLR.lean :: FABL.probabilityDensityCorrelation_add_le_one_add_bias -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Two Fourier Correlations

**Claim.** For distinct indices, the sum of the two density-weighted correlations of a sign-valued function with the corresponding Walsh characters is at most $1+\varepsilon$.

**Proof.** First, distinctness of $\gamma$ and $\eta$ implies $\gamma+\eta\ne0$: if their sum were zero, then in characteristic two each coordinate would satisfy $\gamma_i=\eta_i$, contradicting distinctness. The bias hypothesis therefore bounds the absolute value of the Fourier coefficient of the density at $\gamma+\eta$ by $\varepsilon$. At each point, the function value and both Walsh character values are signs. For any three signs $a,u,v$, one has $au+av\le 1+uv$; apply this with $a=F(x)$ and the two character values. Multiply this pointwise inequality by the nonnegative density and take uniform expectation, using nonnegativity of the density (`ProbabilityDensity.nonneg`). The left side becomes the sum of the two correlations. The right side is the expectation of the density, plus its correlation with the product of the two characters. The characters multiply to the character indexed by $\gamma+\eta$ (`vectorWalshCharacter_mul`), and the density has expectation one (`ProbabilityDensity.expect_eq_one`). The remaining correlation is the Fourier coefficient at $\gamma+\eta$ (`vectorFourierCoeff_eq_expect`), so it is at most its absolute value, hence at most $\varepsilon$. Combining these bounds gives $1+\varepsilon$.

**Key facts.** `FABL.ProbabilityDensity.nonneg`, `FABL.vectorWalshCharacter_mul`, `FABL.ProbabilityDensity.expect_eq_one`, `FABL.vectorFourierCoeff_eq_expect`.
