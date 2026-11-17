<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.cfgPos_cellIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Cell Index Decoding

**Claim.** For an offset $r<2T+1$, the index assigned to time $t$, tape $\tau$, and offset $r$ decodes as the work-cell position $(t,\tau,r)$.

**Proof.** Let $o=\tau(2T+1)+r$ be the within-row offset. The offset is below the stride by `cell_off_lt`, so division with remainder by the stride (`div_mod_stride`) recovers quotient $t$ and remainder $o$. Within the work-cell region, dividing $o$ by $2T+1$ recovers $\tau$, because $r$ is smaller than that block width; taking the remainder recovers $r$. Thus the first region in the definition of the decoder applies, and its time, tape, and offset components are exactly $t$, $\tau$, and $r$.

**Key facts.** `Complexity.cell_off_lt`, `Complexity.div_mod_stride`.
