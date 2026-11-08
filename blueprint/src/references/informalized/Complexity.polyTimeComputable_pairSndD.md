<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_pairSndD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Second Projection

**Claim.** The total second projection on bit strings, which returns the suffix following the first aligned separator $01$ after a sequence of doubled-bit blocks and returns the empty word if parsing fails, is polynomial-time computable.

**Proof.** The machine supplied by the second-projection computation theorem computes this total projection in time bounded by a linear function of the input length. A linear bound is a polynomial bound, by the general result that every function computable in linear time is polynomial-time computable (`polyTimeComputable_of_linear`).

**Key facts.** `Turing.FinTM.computesFunInTime_pairSnd`, `Complexity.polyTimeComputable_of_linear`.
