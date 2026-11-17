<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FuncIndexing/LowerBound.lean :: CommunicationComplexity.Functions.Indexing.answerSet_card_le_pow_cost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Answer-vector count bound

**Claim.** The number of distinct answer vectors of a deterministic one-way indexing protocol is at most $2^c$, where $c$ is its communication cost.

**Proof.** Each answer vector is obtained from some message by applying the decoder at every index. Thus the map from messages to answer vectors can have no more distinct outputs than there are messages. By definition, the cost is the ceiling of the base-two logarithm of the message count, and the message count is at most two to that power. Combining these bounds proves the result.
