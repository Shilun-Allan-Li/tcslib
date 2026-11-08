<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.one_div_learningConsequencesThreshold_sq_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Inverse Threshold Bound

**Claim.** Under the stated regime assumptions, the square of the inverse learning threshold is bounded by the displayed power of $2$.

**Proof.** First, the inverse-threshold estimate bounds the quantity by the rational image of $(8(C+1)(Q+1))^4s^4 9^{2As$, where $s=\sqrt{\lceil\log_2(n+1)\rceil}+1$ and $A$ is the degree coefficient (`FABL.one_div_learningConsequencesThreshold_sq_le_expression`). The integer expression is at most $2^{Bs}$, where $B$ is the singleton exponent coefficient (`FABL.learningConsequencesSingletonExpression_le_two_pow`). Since the natural-number inequality remains valid after casting to the rationals, combining the two bounds proves the result.

**Key facts.** `FABL.one_div_learningConsequencesThreshold_sq_le_expression`, `FABL.learningConsequencesSingletonExpression_le_two_pow`.
