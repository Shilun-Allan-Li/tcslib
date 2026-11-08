<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Fourier.lean :: BooleanAnalysis.ThresholdFunctions.le_fourierWeightUpTo_of_l1_l2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree Fourier weight bound

**Claim.** Under the stated norm inequality for degree-at-most-$k$ coefficient families, any degree-at-most-$k$ polynomial threshold function has Fourier weight through degree $k$ at least $c$.

**Proof.** Choose a degree-at-most-$k$ polynomial $p$ representing $f$. If $p=0$, its threshold is the constant function $1$, so its Fourier weight through degree $k$ is $1$; the claim follows from $c\le 1$ (the zero-representation fact, `fourierWeightUpTo_of_rep_zero`). Otherwise, let $A=\sum_S p(S)^2$, which is positive because $p$ is nonzero (`sum_sq_pos`). The assumed norm inequality gives $cA\le (\mathbb E|p|)^2$. The threshold representation and degree bound also give $(\mathbb E|p|)^2\le A W_{\le k}[f]$ (`sq_expect_abs_le_mul_fourierWeightUpTo`). Hence $cA\le A W_{\le k}[f]$; dividing by the positive number $A$ yields the result.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.fourierWeightUpTo_of_rep_zero`, `BooleanAnalysis.ThresholdFunctions.sum_sq_pos`, `BooleanAnalysis.ThresholdFunctions.sq_expect_abs_le_mul_fourierWeightUpTo`.
