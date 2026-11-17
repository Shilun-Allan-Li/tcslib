<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSoundInput.lean :: Complexity.Meyer.sound_numeric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the Numeric Checks

**Claim.** If all prescribed numerical checks hold and the encoded input bits agree with $x$, then after $2^W-1$ steps the machine is halted and its output register records exactly one true bit.

**Proof.** Set $t=2^W-1$. Since $2^W>0$, this time lies below $2^W$. The final-check instance of the assumed numerical conditions says that the encoded answer for the halted state with a one-bit-true output register is true. On the other hand, the correctness theorem for the numerical encoding (`Complexity.Meyer.correct_all`), applied at time $t$, says that this encoded answer agrees with the actual machine configuration's state and output register. Consequently that configuration has state absent and output register `one true`, as claimed.

**Key facts.** `Complexity.Meyer.NumVal_ans`, `Complexity.Meyer.correct_all`.
