<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Estimation.lean :: FABL.goldreichLevinStageEstimateProgram_covers -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coverage of Stage Estimates

**Claim.** Every possible output trace of the stage contains, for each candidate frequency, a record with the stage coordinate set and that frequency as its key.

**Proof.** Fix a candidate frequency. The output-key theorem identifies the list of keys in the outcome trace with the list of all stage keys (`goldreichLevinStageEstimateProgram_output_keys`). Since the chosen frequency is a candidate, its stage key occurs in that list. It therefore occurs among the keys of the output trace, so some record in the trace has that key. By the definition of a record key and of matching, this record matches the stage coordinate set and the chosen frequency.

**Key facts.** `FABL.goldreichLevinStageEstimateProgram_output_keys`.
