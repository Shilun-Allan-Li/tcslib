<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.exists_deletedLayer1_of_eval_ne_truncateWidth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A deleted gate witnesses changed evaluation

**Claim.** If a layered circuit and its width truncation have different values at an input, then some deleted first-layer gate evaluates to a value different from the neutral value of the dual gate type.

**Proof.** Assume instead that every deleted first-layer gate evaluates to the neutral value of the dual gate type. The circuit evaluation invariance lemma for width truncation then says that the truncated circuit and the original circuit have the same value at the input. This contradicts the assumed difference in their evaluations. Therefore at least one deleted gate has a nonneutral value, as required.

**Key facts.** `FABL.DepthCircuit.eval_truncateWidth_eq_of_deleted_neutral`.
