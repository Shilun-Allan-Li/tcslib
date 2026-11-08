<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.juntaNodeDecision_isBad_empty_of_rootFinderBad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Root-Finder Failure at the Empty Restriction

**Claim.** If the root-finder outcome is bad, then it is a bad decision for the empty-set restriction with the specified fixed assignment.

**Proof.** If the outcome is absent, it is bad by definition. Suppose it is a constant decision. If that decision were correct, the empty-set restriction would be constantly equal to its value. Every cube input is recovered from its free part under the empty restriction, by `juntaRestriction_empty_juntaFreePart`; hence the target would take that same value on every input. This contradicts the assumed nonconstancy, so the decision is bad. Finally, suppose the outcome selects a coordinate. Root-finder badness says that this coordinate is not relevant to the target. If it were relevant to the empty-set restriction, `isRelevant_of_isRelevantJuntaRestriction_empty` would imply that it is relevant to the target, a contradiction. Thus this decision, too, is bad.

**Key facts.** `FABL.juntaRestriction_empty_juntaFreePart`, `FABL.isRelevant_of_isRelevantJuntaRestriction_empty`.
