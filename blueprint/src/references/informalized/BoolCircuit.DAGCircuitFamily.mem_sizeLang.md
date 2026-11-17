<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdjBasic.lean :: BoolCircuit.DAGCircuitFamily.mem_sizeLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the size language

**Claim.** The encoding of $n$ copies of $1$ paired with the binary representation of $i$ belongs to the size language exactly when $i<\mathrm{size}(C_n)$.

**Proof.** Membership in the size language supplies witnesses $n',i'$ for which the encoded pair is the given word and $i'<\mathrm{size}(C_{n'})$. Injectivity of the encoding of a unary length and suffix identifies $n'=n$ and the binary suffixes (pairEncode_replicate_inj). Injectivity of the binary representation then gives $i'=i$ (Complexity.LogProg.bits_injective), yielding the claimed inequality. Conversely, if $i<\mathrm{size}(C_n)$, these same $n,i$ are witnesses in the definition of the size language.

**Key facts.** `Turing.pairEncode_replicate_inj`, `Complexity.LogProg.bits_injective`.
