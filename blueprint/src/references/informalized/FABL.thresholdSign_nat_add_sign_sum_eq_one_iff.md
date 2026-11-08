<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.thresholdSign_nat_add_sign_sum_eq_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold of a Natural Offset Sign Sum

**Claim.** For natural numbers $k,m$ and a sign vector $y\in\{-1,1\}^m$, the threshold sign of $k+\sum_{j=0}^{m-1}y_j$ is $1$ exactly when $-(k+1)<\sum_{j=0}^{m-1}y_j$, with the sum on the right taken in the integers.

**Proof.** First identify the real sum of the sign values with the real cast of their integer sum. If $k+\sum_j y_j$ is nonnegative, its threshold sign is $1$ (`thresholdSign_of_nonneg`), and the corresponding integer inequality is equivalent to $-(k+1)<\sum_j y_j$. If the real quantity is negative, its threshold sign is $-1$ (`thresholdSign_of_neg`), so it is not $1$; in this case the same integer inequality is false. Casting the real comparison to integers and rearranging yields these equivalences.

**Key facts.** `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`.
