<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.tabFun_query -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Evaluation

**Claim.** On the query encoding of a selector and three Boolean lists, the tabulation function returns the selector's answer on the machine configuration reached after the time represented by the first list, with lookahead represented by the second.

**Proof.** Evaluate the tabulation function on the encoded query. The parsing identity says that parsing this encoding returns exactly the encoded selector bits and the three lists (query parsing identity, `Complexity.Meyer.parseQ_query`). Thus the successful branch of the tabulation function applies its definition to those fields. Its decoded selector and simulated configuration are the ones used in the claimed query evaluation, and the resulting table answer is the stated value.

**Key facts.** `Complexity.Meyer.parseQ_query`.
