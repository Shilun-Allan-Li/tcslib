<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satEval_skip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skipping the Second Copy of a Bit

**Claim.** When the skip flag is set, one evaluator step advances the input head by one, clears the skip flag, and preserves the phase, bits, certificate head, saved work tapes, and output.

**Proof.** With the skip flag set, the evaluator's transition is the action that moves the input head right and leaves the certificate head and work tapes unchanged, entering the same phase with the skip flag cleared. Since $i<|w|$, this rightward move advances the canonical input position from $i$ to $i+1$ without reaching the right boundary (`Turing.moveInputPos_pos_of_ne_right`). Applying this action to the canonical configuration gives exactly the stated next configuration (`Complexity.satEvalAction_apply`).

**Key facts.** `Turing.moveInputPos_pos_of_ne_right`, `Complexity.satEvalAction_apply`.
