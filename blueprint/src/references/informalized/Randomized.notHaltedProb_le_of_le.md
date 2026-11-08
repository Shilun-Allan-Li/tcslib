<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.notHaltedProb_le_of_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Nonhalting Probability

**Claim.** If halting is prefix stable and $s\le t$, then the nonhalting probability at length $t$ is at most the nonhalting probability at length $s$.

**Proof.** View a uniformly random length-$t$ string through its first $s$ bits. The probability of an event depending only on those first $s$ bits is unchanged by this restriction (`Randomized.randProb_take`). If the procedure has not halted on the full string, prefix stability implies that it has not halted on its length-$s$ prefix: otherwise a halt on that prefix would persist to the full string. Thus the full-string nonhalting event is contained in the prefix nonhalting event, and monotonicity of probability under inclusion (`Randomized.randProb_mono`) gives the result.

**Key facts.** `Randomized.randProb_take`, `Randomized.IsPrefixStable.take_eq_none`, `Randomized.randProb_mono`.
