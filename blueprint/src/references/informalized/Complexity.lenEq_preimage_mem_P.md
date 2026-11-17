<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.lenEq_preimage_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal output lengths form a polynomial-time language

**Claim.** For polynomial-time computable functions $f,g$ on finite binary strings, the inputs $z$ satisfying $|f(z)|=|g(z)|$ form a language in $\mathsf{P}$.

**Proof.** First compute the paired encoding of $f(z)$ and $g(z)$. The pairing of two polynomial-time computable functions is polynomial-time computable (`Complexity.PolyTimeComputable.pairEncode`). The language of encodings whose two decoded components have equal length is in $\mathsf{P}$ (`Complexity.lenEq_mem_P`). The polynomial-time preimage theorem (`Complexity.preimage_mem_P`) then puts the inputs whose paired encoding belongs to that language in $\mathsf{P}$. By the defining behavior of the pair encoding and total decoder, its decoded components are exactly $f(z)$ and $g(z)$, so this preimage is the language claimed.

**Key facts.** `Complexity.PolyTimeComputable.pairEncode`, `Complexity.lenEq_mem_P`, `Complexity.preimage_mem_P`.
