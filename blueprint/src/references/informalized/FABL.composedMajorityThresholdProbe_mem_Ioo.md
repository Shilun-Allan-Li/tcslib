<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.composedMajorityThresholdProbe_mem_Ioo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold Probe Interval

**Claim.** If $0<\epsilon<1/4$, then $(\sqrt{\epsilon}+1/2)/2$ lies strictly between $0$ and $1/2$.

**Proof.** Since $\epsilon>0$, its square root is positive. Also, $\epsilon<1/4$ implies $\sqrt{\epsilon}<1/2$, because both quantities are nonnegative and squaring preserves their order. Thus the numerator $\sqrt{\epsilon}+1/2$ is positive and strictly less than $1$, so dividing by $2$ places the probe strictly between $0$ and $1/2$.
