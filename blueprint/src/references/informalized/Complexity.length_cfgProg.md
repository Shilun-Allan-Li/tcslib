<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.length_cfgProg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the configuration program

**Claim.** With stride $S=k(2T+1)+|\ell|+3$, the configuration program over time horizon $T$ has length $(T+1)S$.

**Proof.** The configuration program is formed by mapping one instruction constructor over a range containing $(T+1)S$ indices. Mapping a function over a finite range preserves the range's length. Hence the program has length $(T+1)S$.
