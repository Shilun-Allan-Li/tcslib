<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/RunsStayInLimits.lean :: Light.bounded_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded state from a frame

**Claim.** If each entry of a finite integer list and each value of a memory function has absolute value at most $W$, then the state whose locations are given by the list with zero beyond its end, and whose memory is that function, is bounded by $W$.

**Proof.** The hypothesis on the list entries and nonnegativity of $W$ imply that every defaulted list value, including the zero used beyond the list, has absolute value at most $W$ (Light.AbsLe.abs_getD_le). The memory values already satisfy the required bound by hypothesis. These give respectively the location and memory bounds in the definition of a bounded state.

**Key facts.** `Light.AbsLe.abs_getD_le`.
