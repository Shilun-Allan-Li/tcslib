<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.mem_unaryWitnessLang_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Witness Strings of Fixed Length

**Claim.** The unary string consisting of $n$ copies of $1$ belongs to the unary witness language of $B$ exactly when $B$ contains a bit string of length $n$.

**Proof.** If the unary string belongs to the language, there is a witness length $m$ such that the unary string equals the string of $m$ copies of $1$, together with a string $y$ of length $m$ in $B$. Taking lengths in the equality of unary strings gives $n=m$, so $y$ has length $n$ and remains in $B$. Conversely, any $y$ in $B$ of length $n$ witnesses membership directly, with witness length $n$.
