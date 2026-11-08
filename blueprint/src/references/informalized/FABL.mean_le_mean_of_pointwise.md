<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_le_mean_of_pointwise -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Uniform Mean

**Claim.** If two real-valued functions on the sign cube satisfy $u(x)\le v(x)$ at every input, then the uniform mean of $u$ is at most the uniform mean of $v$.

**Proof.** On the finite sign cube, each uniform mean is the sum of the function’s values divided by the cube’s cardinality. The pointwise inequalities give an inequality between the sums, and division by the positive cardinality preserves that inequality. This is the asserted comparison of means.
