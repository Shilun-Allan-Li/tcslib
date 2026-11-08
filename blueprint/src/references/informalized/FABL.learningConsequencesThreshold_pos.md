<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.learningConsequencesThreshold_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the threshold

**Claim.** For every positive influence bound $t$ and positive learning parameter $\varepsilon$, the threshold $\theta$ is positive.

**Proof.** The internal error $\varepsilon/8$ is positive by the positivity result for the internal error. Its square and the square of $t$ are therefore positive, so their quotient is positive. The remaining factor is $(1/9)^d$, a natural power of a positive number, and is positive. The product of these factors, which is the threshold, is positive.

**Key facts.** `FABL.learningConsequencesInternalError_pos`.
