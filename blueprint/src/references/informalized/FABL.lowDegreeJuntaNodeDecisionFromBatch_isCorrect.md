<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaNodeDecisionFromBatch_isCorrect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Batch Decision

**Claim.** Under accurate Fourier estimates and an exact polynomial hypothesis, the decision constructed from the batch correctly identifies either a relevant free coordinate or a constant restriction.

**Proof.** Let $g$ be the reindexed restriction of the target. First split according to whether the procedure detected a Fourier frequency. If it detected one, the previously established detected-frequency case proves the decision correct. Otherwise, exactness of the learned polynomial hypothesis and the encoding equivalence imply that the Boolean function represented by the learned hypothesis is exactly $g$.

Now split according to whether the learned coefficient function has a nonzero nonconstant monomial. If it does, the soundness of the first-nonconstant-monomial selection shows that the least coordinate in that monomial is relevant to the learned Boolean function. Since that function equals $g$, this coordinate is relevant to $g$; transferring relevance through the reindexing gives a correct relevant-coordinate decision for the original restriction.

If there is no nonzero nonconstant monomial, the same soundness result says that the learned polynomial is its constant coefficient. The exact agreement with $g$ therefore makes $g$ constant with that value. Transferring this constant equality back through the reindexing shows that the original restriction is constant too, so the procedure’s constant decision is correct.

**Key facts.** `FABL.lowDegreeJuntaNodeDecisionFromBatch_isCorrect_of_firstDetected_eq_some`, `FABL.f₂HypothesisBooleanFunction_encoding`, `FABL.firstNonconstantLowDegreeMonomial_sound`, `FABL.isRelevantJuntaRestriction_of_reindexed`, `FABL.juntaRestriction_eq_const_of_reindexed_eq_const`.
