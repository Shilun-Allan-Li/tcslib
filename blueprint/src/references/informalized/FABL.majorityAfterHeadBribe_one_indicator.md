<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.majorityAfterHeadBribe_one_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive bribe tail indicator

**Claim.** For $k,m\ge0$ with $m>0$ and $y\in\{−1,1\}^m$, the indicator that the majority function with bribe $1$ returns $1$ equals the indicator that $m^{-1/2}\sum_{j=1}^m y_j>-(k+1)/\sqrt m$.

**Proof.** The real value of the bribe $1$ is $1$, so the majority threshold is $k+\sum_j y_j$. Its value is $1$ exactly when $-(k+1)<\sum_j y_j$ (FABL.thresholdSign_nat_add_sign_sum_eq_one_iff). The normalized Rademacher sum is $(\sum_j y_j)/\sqrt m$. As $m>0$, the denominator $\sqrt m$ is positive, and multiplying the tail condition $-(k+1)/\sqrt m<(\sum_j y_j)/\sqrt m$ by it gives precisely the same integer inequality. The two indicators therefore agree. (The real sign value of $1$ is $1$ by FABL.signValue_one.)

**Key facts.** `FABL.signValue_one`, `FABL.thresholdSign_nat_add_sign_sum_eq_one_iff`.
