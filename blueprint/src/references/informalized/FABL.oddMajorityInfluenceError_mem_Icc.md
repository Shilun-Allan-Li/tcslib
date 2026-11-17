<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityInfluenceError_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on the Influence Error

**Claim.** For every natural number $m$, the difference between $\binom{2m}{m}/2^{2m}$ and $\sqrt{2/(\pi(2m+1))}$ lies between $0$ and $\sqrt{2/(\pi(2m+1))}/(2m+1)$, inclusive.

**Proof.** The lower bound `oddMajorityInfluenceMain_le` says that the main term is at most the influence, so their difference is nonnegative. For the upper bound, `oddMajorityInfluence_le_main_add` bounds the influence by the main term plus the main term divided by $2m+1$. Subtracting the main term yields the desired upper bound on the error.

**Key facts.** `FABL.oddMajorityInfluenceMain_le`, `FABL.oddMajorityInfluence_le_main_add`.
