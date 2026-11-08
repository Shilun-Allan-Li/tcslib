<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.FinNDTM.outputProb_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Certain output has probability one

**Claim.** If every choice word of length $t$ produces the same output $v$, then the probability of outputting $v$ after $t$ choices is $1$.

**Proof.** Every length-$t$ choice word is represented by a function from the $t$ bit positions to the Boolean alphabet, and its associated word has length $t$. The hypothesis therefore makes the event “the output is $v$” true for every such choice. The probability is unchanged when this event is replaced by the always-true event (`Randomized.randProb_congr`), whose probability is $1$ (`Randomized.randProb_true`).

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_true`.
