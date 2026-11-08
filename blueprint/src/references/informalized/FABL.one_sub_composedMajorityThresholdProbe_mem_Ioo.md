<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.one_sub_composedMajorityThresholdProbe_mem_Ioo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement of the Majority Threshold Probe

**Claim.** For $0<\epsilon<1/4$, the complement of the composed majority threshold probe lies strictly between $1/2$ and $1$.

**Proof.** The probe itself lies strictly between $0$ and $1/2$ (`FABL.composedMajorityThresholdProbe_mem_Ioo`). Subtracting these strict inequalities from $1$ reverses their order, giving $1/2<1-T(\epsilon)<1$.

**Key facts.** `FABL.composedMajorityThresholdProbe_mem_Ioo`.
