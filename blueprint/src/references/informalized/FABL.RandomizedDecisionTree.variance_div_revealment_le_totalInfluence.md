<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.RandomizedDecisionTree.variance_div_revealment_le_totalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance divided by revealment

**Claim.** When the randomized decision tree has positive revealment, the variance of the sign-valued function divided by revealment is at most its total influence.

**Proof.** The variance bound by revealment states that \(\operatorname{Var}(f)\leq \operatorname{Reveal}(T)\,\operatorname{Inf}_{\mathrm{total}}(f)\) (`variance_le_revealment_mul_totalInfluence`). Because revealment is positive, divide both sides by it to obtain the claimed inequality.

**Key facts.** `FABL.RandomizedDecisionTree.variance_le_revealment_mul_totalInfluence`.
