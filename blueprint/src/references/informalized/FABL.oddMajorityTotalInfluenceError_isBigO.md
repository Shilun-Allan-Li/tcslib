<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityTotalInfluenceError_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total influence error is asymptotically bounded

**Claim.** The total influence error for majority on dimension $2m+1$ is $O((2m+1)^{-1/2})$ as $m\to\infty$.

**Proof.** The error lies between zero and $1/\sqrt{2m+1}$ (`oddMajorityTotalInfluenceError_mem_Icc`), so its absolute value equals the error. The identity $(2m+1)^{-1/2}=1/\sqrt{2m+1}$ (`oddArity_rpow_neg_one_half`) therefore bounds its norm by the comparison function itself. This gives the required Big-O estimate with constant $1$.

**Key facts.** `FABL.oddMajorityTotalInfluenceError_mem_Icc`, `FABL.oddArity_rpow_neg_one_half`.
