<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierWeightLimits.lean :: FABL.majorityFourierWeightLimitFactor_le_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Influence Factor Bound

**Claim.** For natural numbers $m,j$ with $j<m$, the stated product of majority influences, multiplied by $(\pi/2)(2m+1)$, is at most the displayed inverse square root.

**Proof.** Set $N=2m+1$ and let $A=1-(2j+2)/N+(2j+1)/N^2$. Algebra using $j<m$ rewrites $A$ as $2(m-j)\cdot2m/N^2$, so $A>0$. The squared-influence estimate bounds each squared influence by the corresponding even-level expression (`FABL.oddMajorityInfluence_sq_le_even`). Multiplying these bounds and simplifying shows that the square of the left-hand factor in the claim is at most $1/A$. The left-hand factor is nonnegative because the influences are positive (`FABL.oddMajorityInfluence_pos`), and $A^{-1/2}$ is nonnegative as well. Since its square is $1/A$, comparison of squares yields the desired inequality.

**Key facts.** `FABL.oddMajorityInfluence_sq_le_even`, `FABL.oddMajorityInfluence_pos`.
