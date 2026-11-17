<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPolyAdvice.lean :: Complexity.splitAtLastTrue_pad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padding after the last true bit

**Claim.** For every Boolean word $u$ and natural number $m$, cutting the word $u$ followed by a true bit and then $m$ false bits at its last true bit returns $u$.

**Proof.** Reverse the input list. The result is $m$ false bits followed by a true bit and then the reversal of $u$. Dropping the initial false bits therefore leaves exactly the true bit followed by the reversal of $u$: this holds for every $m$, by induction, since adding one more leading false bit does not change the result of dropping false bits. The definition of the cut removes the leading true bit and reverses what remains, recovering $u; hence the result is `some u`.
