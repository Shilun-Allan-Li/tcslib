<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.fourierEstimatorFailureBits_le_realRestrictedFourierWeightFailureBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison of failure-bit counts

**Claim.** Under the stated lower bound on $\delta'$, its failure-bit count is at most the real restricted Fourier-weight failure-bit count associated with $\delta$.

**Proof.** The hypothesis gives $\delta'>\min(\delta,1/2)/2$, and positivity of $\delta$ makes the clipped quantity positive. Taking reciprocals with positive denominators yields $2/\delta'\le 4/\min(\delta,1/2)$. The ceiling on the left is therefore at most the ceiling of the right-hand real quantity. Monotonicity of the ceiling and then of the base-two natural logarithm (the function $\operatorname{clog}_2$) gives the claimed comparison.
