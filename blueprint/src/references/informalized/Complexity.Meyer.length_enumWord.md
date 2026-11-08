<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.length_enumWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a bounded binary word

**Claim.** For every natural number $w$ and value $v$, the width-$w$ little-endian binary word of $v$ has length $w$.

**Proof.** Induct on the width $w$, allowing the value $v$ to be arbitrary at each stage. At width zero, the word is empty, so its length is zero. At width $w+1$, the definition places one Boolean digit before the width-$w$ word for the quotient of $v$ by two. By the induction hypothesis the tail has length $w$, and prepending one digit gives length $w+1$.
