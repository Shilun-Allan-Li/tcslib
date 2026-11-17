<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov.lean :: BooleanAnalysis.GaussianSpace.expect_mem_unitInterval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a bounded Boolean function

**Claim.** If a real-valued function on a Boolean cube takes values in $[0,1]$, then its uniform expectation also lies in $[0,1]$.

**Proof.** The pointwise lower bound $0\le f$ and monotonicity of expectation imply $\mathbb E[0]\le\mathbb E[f]$ (\texttt{BooleanAnalysis.ThresholdFunctions.expect_mono}). The expectation of a constant function equals that constant (\texttt{BooleanAnalysis.ThresholdFunctions.expect_const}), so $\mathbb E[0]=0$. Similarly, $f\le1$ gives $\mathbb E[f]\le\mathbb E[1]=1$ by the same monotonicity and constant-function identity. Hence the expectation lies in the unit interval.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.expect_mono`, `BooleanAnalysis.ThresholdFunctions.expect_const`.
