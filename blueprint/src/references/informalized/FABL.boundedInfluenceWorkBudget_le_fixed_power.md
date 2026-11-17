<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.boundedInfluenceWorkBudget_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Work Budget

**Claim.** In the stated sub-square-root influence regime, the work-budget expression is at most the fixed power $K(n+1)^E$, with $K$ and $E$ determined by $C$ and $Q$.

**Proof.** The regime gives $B+1\le(F+1)(n+1)^E$, where $B$ is the family bound, $F$ the family constant, and $E$ the family exponent (`learningConsequencesFamilyBound_add_one_le_fixed_power`). The lower bound on accuracy gives $(1/\epsilon)^{10}\le(Q+1)^{10}$ (`one_div_accuracy_pow_le`). Apply the resource-expression estimate with leading factor $2^{42}$, dimension power $3$, and $M=B$. It yields the bound $2^{42}(F+1)^8(Q+1)^{10}(n+1)^{8E+3}$ (`kmResourceExpression_le_fixed_power`). By the definitions of the work constant and work exponent, this is precisely $K(n+1)^E$ in the statement's notation.

**Key facts.** `FABL.learningConsequencesFamilyBound_add_one_le_fixed_power`, `FABL.one_div_accuracy_pow_le`, `FABL.kmResourceExpression_le_fixed_power`.
