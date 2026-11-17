<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.majority_head_directed_influence_finite_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Sample Majority Influence Error

**Claim.** For positive $m$, each of the two directed influences of majority on $k+m$ signs toward a fixed sign differs from its stated difference of Gaussian upper tails by at most $2C(m^{-1/2}+(k+m)^{-1/2})$, where $C$ is the third-moment Berry–Esseen constant.

**Proof.** Apply the finite-dimensional Berry–Esseen estimate for hamming upper-tail indicators (\texttt{abs_expect_hammingUpperTailIndicator_dimension_le}) at each threshold used in the two comparisons. It bounds the absolute difference between the corresponding cube expectation and Gaussian upper tail by $2C/\sqrt d$ in dimension $d$. Positivity of $m$ permits its use in dimension $m$, and $k+m>0$ permits its use in dimension $k+m$.

For the influence toward $+1$, the formula for majority's directed head influence (\texttt{coalitionalInfluenceToward_majority_head_one}) expresses it as the difference of the cube expectations at the plus-bribe threshold and at $-1/\sqrt{k+m}$. Subtract the corresponding difference of Gaussian tails. The result is the difference of the two individual expectation-to-tail errors, so the triangle inequality bounds its absolute value by the sum of their Berry–Esseen bounds, namely $2C(m^{-1/2}+(k+m)^{-1/2})$.

For the influence toward $-1$, use the analogous expression (\texttt{coalitionalInfluenceToward_majority_head_neg_one}), with the common threshold and the minus-bribe threshold. The same subtraction and triangle inequality give the identical error bound.

**Key facts.** `FABL.abs_expect_hammingUpperTailIndicator_dimension_le`, `FABL.coalitionalInfluenceToward_majority_head_one`, `FABL.coalitionalInfluenceToward_majority_head_neg_one`.
