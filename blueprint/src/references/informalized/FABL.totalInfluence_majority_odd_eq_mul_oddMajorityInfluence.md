<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.totalInfluence_majority_odd_eq_mul_oddMajorityInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Majority Influence Formula

**Claim.** For every $m\ge 0$, the total influence of majority on the $(2m+1)$-dimensional Boolean cube is $(2m+1)\binom{2m}{m}/2^{2m}$.

**Proof.** The total influence of odd-dimensional majority is $(2m+1)$ times the central binomial coefficient $\binom{2m}{m}$ divided by $2^{2m}$ (`FABL.totalInfluence_majority_odd`). The defined odd-majority influence is precisely this binomial-coefficient ratio. Substituting that definition yields the claimed formula.

**Key facts.** `FABL.totalInfluence_majority_odd`.
