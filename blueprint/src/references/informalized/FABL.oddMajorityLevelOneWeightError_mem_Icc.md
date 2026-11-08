<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityLevelOneWeightError_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-one majority weight error bounds

**Claim.** For every $m\ge0$, the level-one majority weight error satisfies $0\le E_m\le \dfrac{2}{\pi(2m+1)}$.

**Proof.** The error is the level-one weight minus $2/\pi$. The lower bound follows from the fact that the level-one majority weight is at least $2/\pi$ (`two_div_pi_le_fourierWeightAtLevel_one_majority_odd`). For the upper bound, the level-one weight is at most $2/\pi+2/(\pi(2m+1))$ (`fourierWeightAtLevel_one_majority_odd_le`); subtracting $2/\pi$ gives the stated bound.

**Key facts.** `FABL.two_div_pi_le_fourierWeightAtLevel_one_majority_odd`, `FABL.fourierWeightAtLevel_one_majority_odd_le`.
