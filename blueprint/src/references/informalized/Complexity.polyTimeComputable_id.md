<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTime.lean :: Complexity.polyTimeComputable_id -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Identity

**Claim.** The identity function on bit strings is polynomial-time computable.

**Proof.** A machine computing the identity is available with linear time bound $C(|x|+1)$ for some constant $C$ (`FinTM.computesFunInTime_id`). A linear bound of this form is the polynomial bound with exponent one. Hence this machine also computes the identity within a polynomial time bound, giving the claim; the proof uses monotonicity of computation time to pass to that bound (`ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.computesFunInTime_id`, `Turing.FinTM.ComputesInTime.mono`.
