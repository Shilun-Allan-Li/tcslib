<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/SmallBiasFourierAlgorithm.lean :: FABL.abs_deterministicSmallBiasFourierEstimate_sub_fourierCoeff_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Fourier Estimate Error

**Claim.** For the deterministic sample associated to a small-bias Fourier input, if the Fourier $1$-norm of $f$ is at most the input’s Fourier bound, then the estimate of the Fourier coefficient at $U$ differs from the true coefficient by at most the input’s target accuracy.

**Proof.** The sample count is positive (`SmallBiasFourierInput.sampleCount_pos`), so the sample set is nonempty and its uniform average is defined. Apply the parameterized small-bias Fourier estimate with target accuracy equal to the input bias $\	exttt{input.bias.epsilon}$ and norm bound equal to $\text{input.fourierBound}$. The input bias is positive (`SmallBiasInput.epsilon_pos`) and at most $1/2$ (`SmallBiasInput.epsilon_le_half`); the Fourier bound is at least $1$ by the input’s hypothesis. The deterministic sample’s density is biased by the target accuracy divided by that Fourier bound (`SmallBiasFourierInput.sample_isBiased`). Thus all hypotheses of the parameterized estimate hold, and it bounds the coefficient error by the target accuracy, which is exactly the input’s stated $\text{epsilon}$.

**Key facts.** `FABL.SmallBiasFourierInput.sampleCount_pos`, `FABL.SmallBiasInput.epsilon_pos`, `FABL.SmallBiasInput.epsilon_le_half`, `FABL.SmallBiasFourierInput.sample_isBiased`, `FABL.abs_smallBiasFourierEstimate_sub_fourierCoeff_le_parameter`.
