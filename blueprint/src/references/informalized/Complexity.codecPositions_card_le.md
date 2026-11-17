<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecPositions_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Codec-position count bound

**Claim.** The number of codec positions is at most $2^k(s+n+2)^{k+1}$, where $k$ is the number of work tapes.

**Proof.** A codec position consists of an input-head location and one window location for each work tape, so its cardinality is $(n+2)(2s+1)^k$. Since $n+2\le s+n+2$ and $2s+1\le 2(s+n+2)$, monotonicity of multiplication and of natural-number powers gives an upper bound of $(s+n+2)(2(s+n+2))^k$. Rewriting this as $(s+n+2)2^k(s+n+2)^k$ yields the claimed bound.
