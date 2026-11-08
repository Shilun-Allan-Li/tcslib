<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: Language.allOnes_inLayeredSIZE_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Layered Size for All Ones

**Claim.** The all-ones language is recognized by a finite-layer Boolean circuit family using only identity, NOT, and unbounded fan-in AND gates, with size at most $n+1$ on inputs of length $n$.

**Proof.** Start with the established family recognizing the all-ones language whose size is at most $1$ at every input length ( `Language.allOnes_inLayeredSIZE_one`). For each $n$, the natural-number inequality $1\le n+1$ holds. Monotonicity of layered-size recognition under pointwise increases of the bound ( `Language.InLayeredSIZE.mono`) therefore gives the claimed bound.

**Key facts.** `Language.allOnes_inLayeredSIZE_one`, `Language.InLayeredSIZE.mono`.
