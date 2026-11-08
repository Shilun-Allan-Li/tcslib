<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_right_clamp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Boundary Detection

**Claim.** The input head reads no symbol and is not at position zero exactly when it is at the right boundary, position $|x|+1$.

**Proof.** The input-blank characterization says that the head reads no symbol exactly at position $0$ or position $|x|+1$ (`recordStep_input_blank`). If the head is at zero, the left-hand conjunction is false. If it is at the right boundary, it reads no symbol and is not at zero, so the conjunction is true. At any other position, the characterization says the head reads a symbol, making the conjunction false. These cases establish the equivalence.

**Key facts.** `Turing.recordStep_input_blank`.
