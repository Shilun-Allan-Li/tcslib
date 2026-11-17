<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.indicator_innerProduct_le_of_mgf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator Pairing from an Exponential Moment

**Claim.** If $f$ is indicator-valued with positive expectation $\alpha$, and $\mathbb E e^{tg}\le e^b$, then $t\mathbb E[fg]\le\alpha(b-\log\alpha)$.

**Proof.** For each point of the cube, first establish the pointwise bound
\[t f(x)g(x)\le (b-\log\alpha-1)f(x)+\alpha e^{-b}e^{t g(x)}.\]
If $f(x)=0$, this follows from positivity of the exponential term. If $f(x)=1$, rewrite the exponential term on the right as $e^{t g(x)-b+\log\alpha}$. The inequality then follows from $u+1\le e^u$, with $u=tg(x)-b+\log\alpha$. Take expectations of the pointwise inequality, using monotonicity and linearity of expectation (`expect_mono`, `expect_add`, and `expect_const_mul`). The assumed exponential-moment bound controls the exponential term by $\alpha e^{-b}e^b=\alpha$. Combining terms yields $\alpha(b-\log\alpha)$, as required.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_mono`, `BooleanAnalysis.ThresholdFunctions.expect_add`, `BooleanAnalysis.ThresholdFunctions.expect_const_mul`.
