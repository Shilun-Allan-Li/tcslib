<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean :: BoolCircuit.CircuitEval.eq_replicate_leadOnes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decomposition at the first zero

**Claim.** If a Boolean word $c$ contains a zero and $r$ is its number of initial consecutive ones, then $c$ consists of $r$ ones, followed by a zero and then the remaining suffix.

**Proof.** Induct on the word. The empty word cannot contain zero. If the word begins with zero, then it has no initial ones, and the claimed decomposition is the word itself followed by its remaining suffix. If it begins with one, the remaining word still contains zero. Its number of initial ones is one less than that of the whole word. Apply the induction hypothesis to this tail and prepend the initial one; the resulting initial block has the required length and the same first zero and suffix.
