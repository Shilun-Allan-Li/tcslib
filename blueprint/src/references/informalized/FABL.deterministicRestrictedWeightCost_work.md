<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.deterministicRestrictedWeightCost_work -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work component identity

**Claim.** For every restricted-weight input and finite set $S$, the work component of the deterministic restricted-weight cost is the sum of its construction work, query count, and local work for $S$.

**Proof.** The work component of a sum of learning costs is the sum of their work components. The construction term contributes the construction work; the query-batch term contributes the query count, and the final term contributes the local work. Therefore the total is construction work plus the sum of query count and local work, which is the stated expression by associativity of addition.
