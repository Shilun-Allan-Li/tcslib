<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.epsilon_lt_composedMajorityThresholdProbe_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Probe Squared Exceeds Epsilon

**Claim.** For $0<\epsilon<1/4$, one has $\epsilon<\left((\sqrt{\epsilon}+1/2)/2\right)^2$.

**Proof.** Because $\epsilon>0$, its square root is positive; because $\epsilon<1/4$, its square root is less than $1/2$. Therefore $\sqrt{\epsilon}+1/2>2\sqrt{\epsilon}$. Both sides are positive, so squaring preserves the strict inequality. Dividing by $4$ gives $((\sqrt{\epsilon}+1/2)/2)^2>\epsilon$.
