<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.stageWit_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stage witness specification

**Claim.** The witness selected for stage $i$ has length $\text{freshLen}(i,d.\bound)$ and does not occur among the queries made at that stage.

**Proof.** There are fewer queries at this stage than there are Boolean strings of length $\text{freshLen}(i,d.\bound)$, by the stage query-list length bound (`Complexity.stageQ_length`). The finite counting argument `Complexity.exists_length_not_mem` consequently supplies a Boolean string of that length absent from the query list. The selected witness is defined to be such a string, so it has both asserted properties.

**Key facts.** `Complexity.exists_length_not_mem`, `Complexity.stageQ_length`.
