<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/AdderLanguage.lean :: BoolCircuit.length_natToBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a fixed-width bit list

**Claim.** For any natural numbers $k$ and $m$, the list of the lowest $k$ binary digits of $m$ has length $k$.

**Proof.** The list is formed by applying the bit test for $m$ to each index in `Fin k`. Since `Fin k` has $k$ elements, the resulting list has length $k$.
