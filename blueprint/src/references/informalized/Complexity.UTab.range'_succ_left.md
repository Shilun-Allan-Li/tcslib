<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterLayer.lean :: Complexity.UTab.range'_succ_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Formula for Shifted Ranges

**Claim.** For natural numbers $s$ and $n$, the list of the first $n+1$ consecutive natural numbers beginning at $s$ is $[s]$ followed by the list of the first $n$ consecutive numbers beginning at $s+1$.

**Proof.** The standard successor formula for a shifted range says that increasing its length by one adds its starting value at the front and shifts the start of the remaining range by one. Applying this formula with length $n+1$, then simplifying the successor arithmetic, gives $\mathrm{range'}(s,n+1)=[s]\mathbin{::}\mathrm{range'}(s+1,n)$.
