<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.cfgPos_inpIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Position Index Decoding

**Claim.** For $p<N+2$, the index $tS+k(2T+1)+p$, where $S=k(2T+1)+N+3$, decodes as input position $(t,p)$.

**Proof.** The within-row offset $k(2T+1)+p$ is below the stride, so `div_mod_stride` recovers quotient $t$ and that offset as remainder. The offset is at least the size $k(2T+1)$ of the work-cell region, so the decoder does not select a work cell. It is also less than $k(2T+1)+N+2$, by the assumed bound on $p$, so the decoder selects the input-position region. Subtracting the work-cell region's size leaves exactly $p$, giving $(t,p)$.

**Key facts.** `Complexity.div_mod_stride`.
