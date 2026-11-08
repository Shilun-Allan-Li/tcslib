<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean :: Complexity.LogProg.seam_eq_mkCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seam Configuration Decomposition

**Claim.** The configuration formed by adjoining blank work tapes and zero-position heads to the mapped-state configuration is exactly the configuration assembled from those same components.

**Proof.** Both sides have the same state, input-head position, and output by their definitions. Their work-tape functions are both the append of the original work tapes with the constant blank tapes, and their work-head positions are both the append of the original positions with the constant zero positions. Hence all components agree, so the configurations are equal.
