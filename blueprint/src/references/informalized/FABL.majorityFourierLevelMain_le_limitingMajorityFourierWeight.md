<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.majorityFourierLevelMain_le_limitingMajorityFourierWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Main Term Below the Limiting Weight

**Claim.** For every odd positive level $k$, the main Fourier term is at most the limiting majority Fourier weight.

**Proof.** The error between the limiting weight and the main term is nonnegative, by the lower endpoint of its stated interval bound (`FABL.limitingMajorityFourierWeightError_mem_Icc`). Since this error is the limiting weight minus the main term, nonnegativity gives the claimed inequality.

**Key facts.** `FABL.limitingMajorityFourierWeightError_mem_Icc`.
