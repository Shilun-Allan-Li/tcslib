<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.learningConsequencesFamilyBound_add_one_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Family bound with an additive one

**Claim.** Under the subsquare-root regime hypotheses, the family bound plus one is at most the stated fixed-power expression.

**Proof.** The family-size estimate (FABL.learningConsequencesFamilyBound_le_fixed_power) gives $F\le M(n+1)^e$, where $F$ is the family bound, $M=2^{2e}$ is the family constant, and $e$ is the family exponent. Since $n\ge1$, we have $(n+1)^e\ge1$. Thus $F+1\le M(n+1)^e+(n+1)^e=(M+1)(n+1)^e$, as claimed.

**Key facts.** `FABL.learningConsequencesFamilyBound_le_fixed_power`.
