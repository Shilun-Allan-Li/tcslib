<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierWeightLimits.lean :: FABL.fourierWeightAtLevel_majority_le_limitingMajorityFourierWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-majority Fourier weight bound

**Claim.** For odd positive $n$ and $k$ with $2k<n$, majority's level-$k$ Fourier weight is at most $(1+2k/n)$ times the limiting majority Fourier weight at level $k$.

**Proof.** Write $n=2m+1$ and $k=2j+1$, as permitted by oddness. The hypotheses imply $j<m$. The exact formula for odd-dimensional majority weight expresses the level weight as the limiting level weight multiplied by a factor involving the two odd-majority influences. That factor is bounded by a negative one-half power of $1-(k+1)/n+k/n^2$. The elementary estimate `exercise5_24`, applied with these $k,n$ (which satisfy $1\le k$ and $2k\le n$), bounds this power by $1+2k/n$. The limiting Fourier weight is positive for odd levels (`limitingMajorityFourierWeight_pos_of_odd`), so multiplying the factor inequality by it preserves the inequality. The exact formula then gives the claim.

**Key facts.** `FABL.fourierWeightAtLevel_majority_two_mul_add_one_eq_limiting_mul`, `FABL.limitingMajorityFourierWeight_pos_of_odd`, `FABL.majorityFourierWeightLimitFactor_le_rpow`, `FABL.exercise5_24`.
