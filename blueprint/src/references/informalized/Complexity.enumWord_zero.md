<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumWord_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero at Fixed Width

**Claim.** For every natural number $w$, the width-$w$ little-endian binary word of $0$ is the word consisting of $w$ false bits.

**Proof.** Induct on $w$. At width zero both words are empty. At width $w+1$, the first bit tests whether $0$ is odd, so it is false; the remaining word is the width-$w$ word of zero. By induction that tail consists of $w$ false bits, and adding the first false bit gives the list of $w+1$ false bits.
