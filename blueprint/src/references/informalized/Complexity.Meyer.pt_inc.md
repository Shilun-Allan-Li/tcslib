<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue.lean :: Complexity.Meyer.pt_inc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-width increment

**Claim.** The function that returns the fixed-width binary increment of a Boolean word, using the empty word when increment overflows, is polynomial-time computable.

**Proof.** A machine computes the option-valued fixed-width increment in time bounded linearly in the input length, with the empty word as the default output when increment overflows. The linear-time computation theorem (Turing.FinTM.computesFunInTime_incFixed) supplies such a machine and a linear time bound. Every linear time bound is polynomial, so the linear-to-polynomial closure result (Complexity.polyTimeComputable_of_linear) gives the claim.

**Key facts.** `Turing.FinTM.computesFunInTime_incFixed`, `Complexity.polyTimeComputable_of_linear`.
