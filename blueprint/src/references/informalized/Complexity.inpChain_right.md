<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.inpChain_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Boundary of the Input Chain

**Claim.** At position $|w|+1$, the input-chain value after $t$ steps equals the input symbol read by the head in that configuration.

**Proof.** By definition, the input chain at position $|w|+1$ returns the configuration's input symbol whenever the head position is at most $|w|+1$. The head position is a natural number less than $|w|+2$, since it is the value of an element of `Fin (w.length + 2)`. Hence that bound holds, and the chain equals the input symbol.
