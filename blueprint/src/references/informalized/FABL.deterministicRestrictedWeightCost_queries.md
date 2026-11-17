<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.deterministicRestrictedWeightCost_queries -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership query count

**Claim.** For every restricted-weight input and finite set $S$, the membership-query component of the deterministic restricted-weight cost equals the product of the outer and inner sample counts.

**Proof.** By definition, the cost is the sum of a construction cost whose query component is zero and the sum of a query-batch cost and a local-work cost. The query-batch cost has query component equal to the deterministic restricted-weight query count, while the local-work cost has query component zero. Thus the resulting query component is the query count itself, which by definition is the product of the outer and inner counts.
