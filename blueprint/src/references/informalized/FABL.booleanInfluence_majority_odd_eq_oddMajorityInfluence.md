<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.booleanInfluence_majority_odd_eq_oddMajorityInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd majority influence formula

**Claim.** For every nonnegative integer $m$ and coordinate $i$ of the $(2m+1)$-dimensional cube, the influence of majority equals the odd-majority influence.

**Proof.** Apply the odd-dimensional majority influence formula (`booleanInfluence_majority_odd`), which identifies the influence with the central binomial coefficient divided by $2^{2m}$. This is exactly the definition of odd-majority influence.

**Key facts.** `FABL.booleanInfluence_majority_odd`.
