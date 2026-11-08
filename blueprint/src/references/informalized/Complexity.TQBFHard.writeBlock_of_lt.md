<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.writeBlock_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing Before the Block

**Claim.** At every position $v<i$, writing a finite bit string starting at position $i$ leaves the bit at $v$ equal to its original value $\sigma(v)$.

**Proof.** At position $v$, the writing rule changes the sequence only if $i\le v$ and $v<i+|\beta|$. Since $v<i$, the first condition fails. The rule therefore returns $\sigma(v)$.
