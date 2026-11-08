<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.cfgPos_snapIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Snapshot Index Decoding

**Claim.** The index $tS+k(2T+1)+N+2$, where $S=k(2T+1)+N+3$, decodes as the snapshot at time $t$.

**Proof.** The offset $k(2T+1)+N+2$ is below the stride, so `div_mod_stride` gives quotient $t$ and this offset as remainder. It is not below the work-cell region's endpoint, nor below the input-position region's endpoint: it equals the latter endpoint exactly. Consequently neither of the decoder's first two regions applies, and the decoder returns the snapshot at quotient time $t$.

**Key facts.** `Complexity.div_mod_stride`.
