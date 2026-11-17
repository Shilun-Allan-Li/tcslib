<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdjBasic.lean :: BoolCircuit.DAGCircuitFamily.mem_typeLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in a gate type language

**Claim.** The encoding of $n$ copies of $1$ paired with the binary representation of $i$ belongs to the type language for $t$ exactly when $i<\mathrm{size}(C_n)$ and vertex $i$ of $C_n$ has type $t$.

**Proof.** Membership in the type language supplies witnesses $n',i'$ such that the encoded pair agrees with the given word, $i'<\mathrm{size}(C_{n'})$, and vertex $i'$ has type $t$. Injectivity of the encoding of a unary length and suffix identifies $n'=n$ and the binary suffixes (pairEncode_replicate_inj). Injectivity of the binary representation gives $i'=i$ (Complexity.LogProg.bits_injective), so both required conditions follow. Conversely, if those two conditions hold, choosing $n,i$ as witnesses in the language definition proves membership.

**Key facts.** `Turing.pairEncode_replicate_inj`, `Complexity.LogProg.bits_injective`.
