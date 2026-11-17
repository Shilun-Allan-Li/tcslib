<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.length_padSrcs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Padded Bit Sources

**Claim.** If the source list has length at most the configuration arity, padding it with false constants gives a list whose length is exactly the configuration arity.

**Proof.** Let $N$ be the configuration arity and let $m=|l|$. Padding appends $N-m$ false constants. The hypothesis $m\le N$ ensures this count is nonnegative, and the padded length is $m+(N-m)=N$.
