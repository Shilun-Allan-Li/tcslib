<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.writeBlock_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing an Empty Block

**Claim.** Writing an empty block into a bit sequence starting at any position leaves the sequence unchanged.

**Proof.** The two functions agree at every position $v$. For an empty block, the interval in which writing would change the sequence is specified by $i\le v<i+0$, which is impossible. Hence the definition returns the original bit $\sigma(v)$ at every position, so the functions are equal.
