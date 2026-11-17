<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.parityFunction_isRealSumOfLinearThresholds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity as a Sum of Linear Thresholds

**Claim.** For every coordinate subset $S$, the parity function on $S$ is a real constant plus a sum of $2n$ real-valued linear threshold functions on the Boolean cube.

**Proof.** Use the parity count profile, which assigns to each input the value determined by the number of positive coordinates of that input within $S$. The parity function agrees with this profile by the count formula (parityFunction_eq_parityCountProfile). The representation theorem for functions depending only on this count supplies a real constant and a sum of $2n$ linear threshold functions representing the profile (isRealSumOfLinearThresholds_of_count_profile). Applying that theorem to the parity profile and transferring the equality to the parity function proves the result.

**Key facts.** `FABL.isRealSumOfLinearThresholds_of_count_profile`, `FABL.parityFunction_eq_parityCountProfile`.
