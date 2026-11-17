<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.deterministicRestrictedWeightCost_randomExamples -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Random-example count

**Claim.** For every restricted-weight input and finite set $S$, the deterministic restricted-weight cost uses zero random examples.

**Proof.** Each cost term in the definition has random-example component zero: this holds for the construction cost, for the query-batch cost, and for the local-work cost. Addition of learning costs adds their random-example components, so the total is $0+ (0+0)=0$.
