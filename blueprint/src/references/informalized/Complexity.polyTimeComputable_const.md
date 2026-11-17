<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Functions Are Polynomial-Time Computable

**Claim.** For every fixed bit string $w$, the constant function sending each input bit string to $w$ is polynomial-time computable.

**Proof.** A machine that outputs the fixed word $w$ on every input computes the constant function in linear time, as witnessed by the constant-function machine result (`Turing.FinTM.computesFunInTime_const`). Every function computable within a linear time bound is polynomial-time computable (`Complexity.polyTimeComputable_of_linear`). Applying that implication to this machine proves the claim.

**Key facts.** `Complexity.polyTimeComputable_of_linear`, `Turing.FinTM.computesFunInTime_const`.
