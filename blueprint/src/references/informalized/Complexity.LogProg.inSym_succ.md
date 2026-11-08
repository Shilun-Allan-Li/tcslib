<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.inSym_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol at a successor position

**Claim.** For every Boolean word $x$ and natural number $j$, the input symbol at position $j+1$ is the $j$th symbol of $x$, or is undefined if that index is out of range.

**Proof.** At position $j+1$, the input-symbol definition does not take its zero-position branch, and subtracting one from the position gives $j$. Thus the result is exactly the optional list entry $x[j]?$, which is undefined when $j$ is outside the word.
