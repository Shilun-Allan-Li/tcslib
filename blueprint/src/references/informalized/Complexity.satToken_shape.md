<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satToken_shape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shape of the Unary Token Split

**Claim.** For every Boolean word $x$, if $(k,y)$ is the length and residual word after removing the longest initial run of true bits, its unary token split is the pair consisting of $k$ true bits followed by the first bit of $y$, if present, and $y$ with that first bit removed. Moreover, $y$ is empty or begins with false.

**Proof.** Induct on the word. The empty word gives an empty token and suffix. If the first bit is false, the initial true run has length zero and that false bit is the token delimiter; the remaining word is the suffix. If the first bit is true, apply the induction hypothesis to the remainder. Prepending this true bit increases the initial-run length by one, while preserving the delimiter and suffix described there. The induction hypothesis also ensures that the residual after the initial run cannot begin with true, so it is empty or begins with false.
