<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.thresholdSign_sign_sum_sub_nat_eq_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold of a Signed Sum Minus an Integer

**Claim.** For natural numbers $k,m$ and a sign vector $y$ on the $m$ coordinates, the threshold sign of the sum of its signs minus $k$ is $1$ exactly when the sum of their integer values is strictly greater than $k-1$.

**Proof.** Rewrite the real sum of sign values as the real cast of their integer sum. If the resulting real quantity, $-k+\sum_j y_j$, is nonnegative, its threshold sign is $1$ (`thresholdSign_of_nonneg`), and this condition rearranges over the integers to $k-1<\sum_j y_j$. If it is negative, the threshold sign is $-1$ (`thresholdSign_of_neg`), and the strict integer inequality fails. The cast preserves the comparisons, so these cases give both directions of the equivalence.

**Key facts.** `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`.
