<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean :: Complexity.unaryExt_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Extension on a Unary Word

**Claim.** For every function $g$ and every natural number $n$, the unary extension of $g$ evaluated at the word of $n$ ones equals $g(n)$.

**Proof.** The input word is $n$ ones, so it equals the replicate of its own length by ones. Thus the defining condition for the unary extension holds, and its value is $g$ of that length, namely $g(n).
