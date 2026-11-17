<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.eval_blockMiddleLayer_get -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Individual middle-gate evaluation

**Claim.** The OR gate associated with clause $i$, fed by the corresponding first-layer AND outputs, equals that clause evaluated on the block-output pattern.

**Proof.** The indexed middle-layer input set is exactly the clause-node input set for the clause at position $i`; this follows by unfolding the mapped middle-layer list. The clause-node evaluation lemma then identifies the OR of the selected first-layer outputs with the clause evaluation on the block-output pattern (`FABL.eval_clauseNodeInputs`). The first-layer length lemma supplies the index conversion needed to interpret those outputs (`FABL.length_blockFirstLayer`).

**Key facts.** `FABL.eval_clauseNodeInputs`, `FABL.length_blockFirstLayer`.
