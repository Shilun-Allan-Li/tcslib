<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.fixedPair_polyTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Fixed-String Pairing

**Claim.** For fixed $\alpha$, the function sending each binary string $x$ to the string formed by doubling each bit of $x$, then appending $01$ and $\alpha$, is polynomial-time computable.

**Proof.** Use the machine that writes the fixed prefix formed by doubling the bits of $\alpha$ and then appending $01$. The fixed-string running-time result (`Complexity.fixedPair_computes`) gives time $2|\alpha|+|x|+3$. This is bounded by $(2|\alpha|+3)(|x|+1)$ for every input length. The machine therefore computes the function within a polynomial time bound, with coefficient $2|\alpha|+3$ and degree $1$; the time-bound monotonicity fact (`Turing.FinTM.ComputesInTime.mono`) permits using this larger bound.

**Key facts.** `Complexity.fixedPair_computes`, `Turing.FinTM.ComputesInTime.mono`.
