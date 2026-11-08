<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Constructible.lean :: Complexity.b3a_seam_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound for Sequential Composition

**Claim.** If $R$ first reaches its exit state at time $a$, then the machine that switches from $R$ to $Q$ at that exit uses through time $a+1+b$ no more space than the sum of the space used by $R$ through time $a$ and by $Q$ through time $b$, started from the configuration $e$ with its state replaced by the entry state.

**Proof.** Fix a work tape. The visited-head inclusion for sequential composition (`seamCompTM_visitedByTapeHead_ofCfg`) places every position visited by the composite run through time $a+1+b$ in the union of the positions visited by $R$ through time $a$ and those visited by $Q$ through time $b$ from the relabeled exit configuration. The cardinality of a union is at most the sum of the two cardinalities. Sum this inequality over the $k$ tapes; finite-sum distributivity identifies the resulting right-hand side with the sum of the two machines' total space usages.

**Key facts.** `Turing.seamCompTM_visitedByTapeHead_ofCfg`.
