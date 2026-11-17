<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.positiveMask_coefficient_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected masked Walsh character

**Claim.** For a uniformly random Boolean vector $r$, the expected masked character is $2^{-|S|}$.

**Proof.** For each fixed $r$, the masked character equals $\prod_{i\in S}\mathbf 1_{\{r_i=0\}}\sigma(r_i)$. For each coordinate, this factor is $(1/2)(1+\sigma(r_i))$: it is $1$ when $r_i=0$ and $0$ when $r_i=1$. Expanding the product gives $2^{-|S|}\sum_{T\subseteq S}\chi_T(r)$. Take expectations term by term. The Walsh characters have mean zero unless their index is empty, in which case the mean is one: this follows from character orthogonality (`fourier_coeff_chi`) together with the constant character identity (`chiS_empty`) and the uniform-cube expectation formula (`expect_eq_fintypeExpect`). Consequently only $T=\varnothing$ survives, leaving $2^{-|S|}$. Pulling the constant through expectation uses linearity (`expect_const_mul`).

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_const_mul`, `BooleanAnalysis.chiS_empty`, `BooleanAnalysis.expect_eq_fintypeExpect`, `BooleanAnalysis.fourier_coeff_chi`.
