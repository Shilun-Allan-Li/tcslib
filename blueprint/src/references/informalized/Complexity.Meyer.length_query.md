<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.length_query -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a query word

**Claim.** The query word formed from a length-$n_b$ bit string, encoded words $t$ and $a$ with their separators, and the word $x$ has length $n_b+2|t|+2|a|+4+|x|$.

**Proof.** The query concatenates the $n_b$ bits, the encoding of $t$, two separator bits, the encoding of $a$, two more separator bits, and $x$. Each encoded word has twice the length of its source (`length_fcode`); concatenation adds lengths, and the four separators contribute four. Adding these contributions gives the stated formula.

**Key facts.** `Complexity.Meyer.length_fcode`.
