<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.enumWord_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Binary Word

**Claim.** For every natural number $w$, the width-$w$ little-endian binary word of $0$ is the word of length $w$ consisting entirely of $0$s.

**Proof.** Induct on $w$. At width zero, both words are empty. At width $w+1$, the least significant bit of zero is false, and dividing zero by two leaves zero. The induction hypothesis says the remaining width-$w$ word consists entirely of false bits. Thus the encoded word is a leading false bit followed by those $w$ false bits.
