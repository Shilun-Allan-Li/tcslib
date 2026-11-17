<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_lengthBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary length computation

**Claim.** The function sending a Boolean word $u$ to the binary expansion of its length is polynomial-time computable.

**Proof.** A machine computes the binary expansion of the input length in time bounded linearly in the input length, by the linear-time length-bits result (Turing.FinTM.computesFunInTime_lengthBits). Since a linear bound is polynomial, the linear-to-polynomial closure result (Complexity.polyTimeComputable_of_linear) yields the claim.

**Key facts.** `Turing.FinTM.computesFunInTime_lengthBits`, `Complexity.polyTimeComputable_of_linear`.
