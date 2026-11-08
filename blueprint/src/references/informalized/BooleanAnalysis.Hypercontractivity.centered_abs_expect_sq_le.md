<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.centered_abs_expect_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive-event bound for centered functions

**Claim.** For a mean-zero function on the Boolean cube, the square of its expected absolute value is at most four times its second moment multiplied by the probability that it is positive.

**Proof.** Let $I$ be the indicator of the event $g>0$. Pointwise, $|g|=2gI-g$: when $g>0$ this reads $g=2g-g$, and when $g\le0$ it reads $-g=0-g$. Taking expectations and using linearity of expectation, including the rule that constants factor out (\texttt{expect\_sub} and \texttt{expect\_const\_mul}), together with $\mathbb E g=0$, gives $\mathbb E|g|=2\mathbb E(gI)$. The indicator satisfies $I^2=I$. Cauchy–Schwarz for finite expectations therefore gives $(\mathbb E(gI))^2\le \mathbb E(g^2)\mathbb E(I^2)=\langle g,g\rangle\Pr[g>0]$. Here expectation agrees with the finite uniform expectation (\texttt{expect\_eq\_fintypeExpect}), so the finite Cauchy–Schwarz inequality applies. Squaring the first identity and applying this bound proves the result.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_sub`, `BooleanAnalysis.ThresholdFunctions.expect_const_mul`, `BooleanAnalysis.expect_eq_fintypeExpect`.
