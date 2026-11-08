<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.enumWord_ones -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# All-Ones Binary Word

**Claim.** For every natural number $w$, the width-$w$ little-endian binary word of $2^w-1$ is the word of length $w$ consisting entirely of $1$s.

**Proof.** Induct on $w$. At width zero, both words are empty. At width $w+1$, the number $2^{w+1}-1$ is odd, so its least significant bit is $1$. Dividing it by two gives $2^w-1$, using $2^w\ge1$. By induction, the remaining width-$w$ word consists entirely of ones. The encoded word is therefore a leading one followed by $w$ ones, as claimed.
