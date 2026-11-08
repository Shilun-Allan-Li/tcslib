<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLCounterexample.lean :: FABL.truncatedNormalizedRademacherSum_violates_boolean_kkl_scale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bound Violates the Boolean Scale

**Claim.** For positive $n$ with $\log n>2400$, every coordinate influence of the truncated normalized Rademacher sum is strictly less than its variance times $\log n/(100n)$.

**Proof.** Fix a coordinate. The influence bound gives an upper bound of $1/n$, while the variance bound gives variance at least $1/24$. Since $\log n>2400$, we have $1<(1/24)\log n/100$. Dividing this strict inequality by the positive quantity $n$ yields $1/n<(1/24)\log n/(100n)$. The logarithm is positive, so the variance lower bound implies $(1/24)\log n/(100n)\le \operatorname{Var}\,\log n/(100n)$. Chaining these inequalities with the influence bound proves the result.

**Key facts.** `FABL.influence_truncatedNormalizedRademacherSum_le`, `FABL.variance_truncatedNormalizedRademacherSum_ge`.
