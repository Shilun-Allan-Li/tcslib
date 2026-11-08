<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaInputBatchSplitEquiv_symm_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstructing a Batch from Its Split

**Claim.** Applying the inverse of the batch-splitting bijection to a batch of fixed assignments and a batch of free assignments returns the batch whose $r$th entry combines the two assignments at $r$.

**Proof.** The inverse map of the stated bijection is defined by sending a pair of batches to the batch whose entry at each index $r$ is the combination of the fixed and free assignments at that same index. Evaluating the inverse on the given pair therefore yields the claimed batch, directly from the definition.
