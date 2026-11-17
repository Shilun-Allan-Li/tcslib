<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.dbl_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Doubling a Unary Word

**Claim.** For every natural number $n$, doubling the word of $n$ ones gives the word of $2n$ ones.

**Proof.** Induct on $n$. At $n=0$, both sides are empty. For the successor case, the input word consists of one initial $1$ followed by $n$ ones. Doubling distributes over this list decomposition: the first bit contributes two ones, and by the induction hypothesis the remaining part contributes $2n$ ones. Concatenating these gives $2n+2=2(n+1)$ ones, as required.
