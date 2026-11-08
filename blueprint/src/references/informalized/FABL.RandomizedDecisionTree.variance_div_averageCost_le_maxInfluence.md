<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.RandomizedDecisionTree.variance_div_averageCost_le_maxInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance divided by average cost

**Claim.** When the randomized decision tree has positive average cost, the variance of the sign-valued function divided by that cost is at most its maximum coordinate influence.

**Proof.** The variance bound by maximum influence gives \(\operatorname{Var}(f)\leq \operatorname{Inf}_{\max}(f)\,\operatorname{Cost}_{\mathrm{avg}}(T)\) (`variance_le_maxInfluence_mul_averageCost`). Since the average cost is positive, division by it preserves the inequality and yields the asserted bound.

**Key facts.** `FABL.RandomizedDecisionTree.variance_le_maxInfluence_mul_averageCost`.
