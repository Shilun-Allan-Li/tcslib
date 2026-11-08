<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdjBasic.lean :: BoolCircuit.DAGCircuitFamily.mem_edgeLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the edge language

**Claim.** The encoding of the unary string of length $n$ paired with the binary representations of $i$ and $j$ belongs to the edge language exactly when vertex $i$ is an argument of the gate at vertex $j$ in the $n$-input circuit, with $j$ a gate vertex.

**Proof.** By definition of the edge language, membership supplies some indices $n',i',j'$ whose corresponding encoding is the given word and for which the edge relation holds. Injectivity of the paired encoding of a unary length and a suffix identifies $n'=n$ and the inner paired encoding (pairEncode_replicate_inj). Injectivity of the pairing then identifies the two binary index strings (pairEncode_injective), and injectivity of the binary representation identifies their indices, so $i'=i$ and $j'=j$ (Complexity.LogProg.bits_injective). The supplied edge relation is therefore precisely the required one. Conversely, if that edge relation holds, choosing the given $n,i,j$ as the witnesses in the definition of the edge language proves membership.

**Key facts.** `Turing.pairEncode_replicate_inj`, `Turing.pairEncode_injective`, `Complexity.LogProg.bits_injective`.
