<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Estimation.lean :: FABL.goldreichLevinStageEstimateProgram_output_keys -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Keys of Stage Output Records

**Claim.** For every possible stage outcome, the sequence of keys of its output records is exactly the list of stage coordinate-frequency pairs in candidate order.

**Proof.** The stage program is the sequence of candidate-estimation programs, one for each key in the candidate list. Each individual candidate estimator returns records whose key is the requested pair (`goldreichLevinCandidateEstimateProgram_key`). The sequence mapping result states that, when every component program returns its requested key, the list of output keys equals the list of requested items (`LearningProgram.map_output_eq_of_mem_support_sequence`). Applying it to the stage's list of coordinate-frequency pairs gives the asserted equality.

**Key facts.** `FABL.LearningProgram.map_output_eq_of_mem_support_sequence`, `FABL.goldreichLevinCandidateEstimateProgram_key`.
