<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLR.lean :: FABL.two_mul_derandomizedBLRAcceptanceProbability_sub_one_le_of_half_le_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Bound from a Large Fourier Coefficient

**Claim.** For a nonnegative density $\phi$ of uniform mean $1$ and a Boolean function $f$, if every nonzero Fourier coefficient of $\phi$ has absolute value at most $\varepsilon$, then any coefficient of the sign encoding of $f$ whose square is at least $1/2$ yields the stated upper bound on twice the derandomized BLR acceptance probability minus one.

**Proof.** Write $F(x)=(-1)^{f(x)}$, let $w_\gamma=\widehat F(\gamma)^2$, and let $r_\gamma$ be the correlation of $F$ against the Walsh character indexed by $\gamma$, averaged with density $\phi$. The sign-valuedness of $F$ follows from `FABL.isSignValued_realSignEncodedFunction`, and Parseval gives $\sum_\gamma w_\gamma=1$ by `FABL.sum_sq_vectorFourierCoeff_eq_one`. Each $r_\gamma\leq1$: pointwise, $F$ times a Walsh character has absolute value $1$ by `FABL.abs_vectorWalshCharacter`, and multiplying by the nonnegative density and averaging preserves the upper bound; the density has mean $1$ by `FABL.ProbabilityDensity.expect_eq_one` and its pointwise nonnegativity is `FABL.ProbabilityDensity.nonneg`.

For every $\gamma\ne\gamma_0$, the biased-density correlation inequality `FABL.probabilityDensityCorrelation_add_le_one_add_bias` gives $r_\gamma+r_{\gamma_0}\leq1+\varepsilon$. Thus $r_\gamma\leq1+\varepsilon-r_{\gamma_0}$. The acceptance expansion `FABL.two_mul_derandomizedBLRAcceptanceProbability_sub_one_eq_sum_sq_mul_correlation` expresses the quantity to bound as $\sum_\gamma w_\gamma r_\gamma$. Separate the $\gamma_0$ term; on all other terms use the preceding correlation bound and $w_\gamma\geq0$. Since the weights sum to $1$, this yields
\[(1-w_{\gamma_0})(1+\varepsilon-r_{\gamma_0})+w_{\gamma_0}r_{\gamma_0}.\]
Finally, $w_{\gamma_0}\geq\tfrac12$ by hypothesis and $r_{\gamma_0}\leq1$. Expanding the difference between this expression and $\varepsilon+(1-\varepsilon)w_{\gamma_0}$ shows it is $-(2w_{\gamma_0}-1)(1-r_{\gamma_0})\leq0$, proving the claim.

**Key facts.** `FABL.isSignValued_realSignEncodedFunction`, `FABL.sum_sq_vectorFourierCoeff_eq_one`, `FABL.ProbabilityDensity.expect_eq_one`, `FABL.ProbabilityDensity.nonneg`, `FABL.abs_vectorWalshCharacter`, `FABL.probabilityDensityCorrelation_add_le_one_add_bias`, `FABL.two_mul_derandomizedBLRAcceptanceProbability_sub_one_eq_sum_sq_mul_correlation`.
