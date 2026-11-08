<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_bits_length_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary length under power-of-two scaling

**Claim.** For natural numbers $C,c,n,m$ with $n\le m$, the binary expansion of $C\cdot 2^{(n+1)^c}$ has length at most $(m+1)^c$ plus the length of the binary expansion of $C$.

**Proof.** If $C=0$, both binary expansions are empty, so the bound holds. Otherwise, the binary-shift formula says that multiplying $C$ by $2^p$ prepends $p$ zero bits to its binary expansion (\texttt{e3_bits_shift}). Taking lengths with $p=(n+1)^c$ therefore gives $(n+1)^c+\operatorname{length}(\mathrm{bits}(C))$. Since $n\le m$, we have $(n+1)^c\le(m+1)^c$ by monotonicity of natural-number powers; adding the fixed length of $\mathrm{bits}(C)$ proves the claim.

**Key facts.** `Complexity.e3_bits_shift`.
