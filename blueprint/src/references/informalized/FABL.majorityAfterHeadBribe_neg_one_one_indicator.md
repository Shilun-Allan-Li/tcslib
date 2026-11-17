<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.majorityAfterHeadBribe_neg_one_one_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative bribe tail indicator

**Claim.** For $k,m\ge0$ with $m>0$ and $y\in\{−1,1\}^m$, the indicator that the majority function with bribe $-1$ returns $1$ equals the indicator that $m^{-1/2}\sum_{j=1}^m y_j>(k-1)/\sqrt m$.

**Proof.** Expanding the negative bribe and using that the real value of $-1$ is $-1$, the majority threshold becomes $-k+\sum_j y_j$. The threshold-sign criterion identifies its being $1$ with the integer inequality $(k-1)<\sum_j y_j$ (FABL.thresholdSign_sign_sum_sub_nat_eq_one_iff). Meanwhile, the normalized Rademacher sum is $(\sum_j y_j)/\sqrt m$: the square root is positive because $m>0$. Multiplication of the strict inequality $(k-1)/\sqrt m< (\sum_j y_j)/\sqrt m$ by this positive square root is equivalent to $(k-1)<\sum_j y_j$. Thus the two indicator conditions are equivalent, and their values agree. (The real sign value of $-1$ is $-1$ by FABL.signValue_neg_one.)

**Key facts.** `FABL.signValue_neg_one`, `FABL.thresholdSign_sign_sum_sub_nat_eq_one_iff`.
