<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.boundedInfluenceQueryBudget_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Query Budget

**Claim.** Under the stated sub-square-root influence regime, the query-budget expression is bounded by the fixed power with constant and exponent determined by $C$ and $Q$.

**Proof.** First, the regime estimate gives the family bound plus one at most $(F+1)(n+1)^E$, where $F$ is the family constant and $E$ the family exponent (`learningConsequencesFamilyBound_add_one_le_fixed_power`). The accuracy hypothesis $1/(Q+1)\le\varepsilon$ also gives $(1/\varepsilon)^{10}\le(Q+1)^{10}$ (`one_div_accuracy_pow_le`). Apply the resource-expression estimate with leading factor $2^{40}$, dimension power $2$, and $M$ equal to the family bound. It combines these two inequalities to bound the left side by $2^{40}(F+1)^8(Q+1)^{10}(n+1)^{8E+2}$ (`kmResourceExpression_le_fixed_power`). Replacing $F$ and $E$ by their definitions yields the asserted query constant and exponent.

**Key facts.** `FABL.learningConsequencesFamilyBound_add_one_le_fixed_power`, `FABL.one_div_accuracy_pow_le`, `FABL.kmResourceExpression_le_fixed_power`.
