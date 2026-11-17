<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityLevelOneWeightError_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-one weight error is asymptotically bounded

**Claim.** The level-one majority weight error is $O((2m+1)^{-1})$ as $m\to\infty$.

**Proof.** The error lies between zero and $2/(\pi(2m+1))$ (`oddMajorityLevelOneWeightError_mem_Icc`). Thus its absolute value is the error itself. The identity $(2m+1)^{-1}=1/(2m+1)$ (`oddArity_rpow_neg_one`) turns the upper bound into $(2/\pi)(2m+1)^{-1}$. This uniform constant bound is precisely the asserted Big-O estimate.

**Key facts.** `FABL.oddMajorityLevelOneWeightError_mem_Icc`, `FABL.oddArity_rpow_neg_one`.
