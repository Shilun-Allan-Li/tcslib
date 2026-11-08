<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.charFun_normalizedCorrelatedSignSumMeasure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characteristic Function of a Normalized Sum

**Claim.** For [?]a nonnegative integer $n$, the characteristic function of the normalized sum of $n$ independent correlated sign vectors at $t$ is the $n$th power of the characteristic function of one vector, evaluated at $(\\sqrt n)^{-1}t$.

**Proof.** Write the normalized sum as the scalar multiple $(\sqrt n)^{-1}$ of the unnormalized sum. The characteristic function of the image of a measure under scalar multiplication is the original characteristic function evaluated at the correspondingly scaled argument. Next, the characteristic function of a sum of independent vectors, whose joint law is the product measure, is the product of their characteristic functions. Since each coordinate has the same correlated sign-vector measure, this product consists of $n$ identical factors, giving the stated $n$th power.
