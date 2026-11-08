<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.bit_rep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bit in a unary run

**Claim.** If dropping the first $p$ bits of $E$ leaves $k$ true bits followed by a false bit and a suffix, then for every $j\le k$, the bit at position $p+j$, defaulting to false out of range, is true exactly when $j<k$.

**Proof.** The bit at position $p+j$ in $E$ is the bit at position $j$ in the string obtained by dropping its first $p$ bits. By the assumed decomposition, that string is $k$ true bits followed by a false bit and the suffix. If $j<k$, the selected bit is among the initial true bits. If $j=k$, it is the following false bit; these are the only possibilities because $j\le k$. Hence the defaulted bit agrees with the truth value of $j<k$.
