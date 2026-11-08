<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.SmallBiasInput.epsilon_le_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bias at Most One Half

**Claim.** For a small-bias input whose numerator is positive and whose doubled numerator is at most its denominator, the bias parameter is at most $1/2$.

**Proof.** The denominator is positive because it is at least twice the positive numerator. After casting to the reals, the assumed inequality gives twice the numerator at most the denominator. Dividing by the positive denominator shows that twice the bias parameter is at most $1$, which is equivalent to the bias being at most $1/2$.
