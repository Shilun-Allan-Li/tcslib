<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PClosure.lean :: Complexity.lenLe_preimage_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output-length comparison is polynomial-time decidable

**Claim.** For polynomial-time computable functions $f,g$ on finite binary strings, the inputs $z$ satisfying $|g(z)|\le |f(z)|$ form a language in $\mathsf{P}$.

**Proof.** Encode the pair of outputs $f(z),g(z)$. Pairing polynomial-time computable functions preserves polynomial-time computability (`Complexity.PolyTimeComputable.pairEncode`). The language of pair encodings whose second decoded component has length at most the first belongs to $\mathsf{P}$ (`Complexity.lenLe_mem_P`). Taking its preimage under the paired computation preserves membership in $\mathsf{P}$ (`Complexity.preimage_mem_P`). The decoded components of this pair encoding are $f(z)$ and $g(z)$, so that preimage is exactly the stated language.

**Key facts.** `Complexity.PolyTimeComputable.pairEncode`, `Complexity.lenLe_mem_P`, `Complexity.preimage_mem_P`.
