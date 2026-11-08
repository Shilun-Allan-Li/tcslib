<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.cfgExp_cellIdx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-cell index expansion

**Claim.** At the index assigned to time $t$, work tape $\tau$, and cell coordinate $r<2T+1$, the configuration expansion equals the work-cell expansion for those parameters.

**Proof.** The indexing lemma identifies the configuration position of this index as the work cell $(t,\tau,r)$ (`Complexity.cfgPos_cellIdx`). By the definition of the configuration expansion, its value at a work-cell position is exactly the corresponding work-cell expansion. Substituting the identified position proves the equality.

**Key facts.** `Complexity.cfgPos_cellIdx`.
