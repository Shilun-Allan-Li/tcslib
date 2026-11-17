<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdBias.lean :: FABL.mean_nonneg_of_nonnegative_linearThresholdBias -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Biased Linear Threshold

**Claim.** If a Boolean function is the threshold sign of an affine linear form whose constant bias is nonnegative, then its uniform mean is nonnegative.

**Proof.** Pair each point \(x\) with its antipode \(-x\). The affine form at the antipode is the bias minus the linear form at \(x\) (\(\texttt{FABL.affineLinearForm_neg_input}\)). For any real \(t\), a nonnegative bias ensures that the two threshold signs at bias plus \(t\) and bias minus \(t\) have sum at least zero (\(\texttt{FABL.thresholdPair_nonneg_of_bias_nonneg}\)). Thus the values of the function at each antipodal pair have nonnegative sum. Taking expectations preserves nonnegativity. Finally, the antipodal map preserves the uniform distribution, so the expectation of \(f(-x)\) equals that of \(f(x)\) (\(\texttt{FABL.expect_neg_input}\)); the expected pair sum is therefore twice the mean of \(f\), which proves the claim.

**Key facts.** `FABL.affineLinearForm_neg_input`, `FABL.thresholdPair_nonneg_of_bias_nonneg`, `FABL.expect_neg_input`.
