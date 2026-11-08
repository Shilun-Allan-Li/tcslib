<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationAdjacency_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacency Formula Evaluation

**Claim.** The adjacency formula on the concatenated encodings of two configurations on the same input is true exactly when the core data of the one-step successor of the first configuration, together with its output summary, equals that of the second.

**Proof.** The length and coefficient hypotheses ensure that the two configuration codes occupy the intended paired wire positions. By the paired-code lookup result (`configurationCodec_pair_get`), evaluating the relabelled formula on their concatenation is therefore the same as evaluating its original formula on the two corresponding code rows. The CNF is a conjunction of the input-equality formula and the transition formula (`CNF.eval_append`). The input-equality formula is true because both rows encode the same input (`codecInputEquality_eval`). The transition formula is true exactly when the successor core and output summary agree with those of the second configuration (`codecTransitionCNF_step_iff`). Thus the conjunction has precisely the claimed truth condition.

**Key facts.** `Complexity.configurationCodec_pair_get`, `Complexity.codecInputEquality_eval`, `Complexity.codecTransitionCNF_step_iff`.
