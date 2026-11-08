<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/Peres.lean :: FABL.totalInfluence_majority_le_main_add_four_div_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Influence Bound

**Claim.** For every positive $n$, the total influence of majority on $n$ coordinates is at most $\sqrt{2/\pi}\sqrt n+4/\sqrt n$.

**Proof.** Split according to whether $n$ is even or odd. If $n$ is even, positivity lets us write $n=2m+2$ for some $m$. Every majority function qualifies as a majority function (`FABL.majority_isMajorityFunction`), so its total influence equals the main term $\sqrt{2/\pi}\sqrt{2m+2}$ plus the even error (`FABL.totalInfluence_evenMajority_eq_main_add_error`). The absolute error is at most $4/\sqrt{2m+2}$ (`FABL.abs_evenMajorityTotalInfluenceError_le`), which gives the desired upper bound. If $n$ is odd, write $n=2m+1$. Its total influence equals the same main term for this dimension plus the odd error (`FABL.totalInfluence_majority_odd_eq_main_add_error`). The odd error is nonnegative and at most $1/\sqrt{2m+1}$ (`FABL.oddMajorityTotalInfluenceError_mem_Icc`), hence in particular at most $4/\sqrt{2m+1}$. This proves the bound in both cases.

**Key facts.** `FABL.majority_isMajorityFunction`, `FABL.abs_evenMajorityTotalInfluenceError_le`, `FABL.totalInfluence_evenMajority_eq_main_add_error`, `FABL.oddMajorityTotalInfluenceError_mem_Icc`, `FABL.totalInfluence_majority_odd_eq_main_add_error`.
