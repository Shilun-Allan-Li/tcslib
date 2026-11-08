<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.two_div_pi_le_fourierWeightAtLevel_one_majority_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-One Majority Fourier Weight Bound

**Claim.** For every natural number $m$, the level-one Fourier weight of majority on $2m+1$ coordinates is at least $2/\pi$.

**Proof.** Write $N=2m+1$, which is positive. The level-one weight identity (`FABL.fourierWeightAtLevel_one_majority_odd`) expresses the weight as $N$ times the square of the odd-majority influence. The main influence is no larger than the odd-majority influence (`FABL.oddMajorityInfluenceMain_le`), and both are nonnegative, so their squares have the same ordering; positivity of the latter is recorded in `FABL.oddMajorityInfluence_pos`. The main influence's square is $2/(\pi N)$ (`FABL.oddMajorityInfluenceMain_sq`), so multiplying it by $N$ gives exactly $2/\pi$. Since $N>0$, multiplying the squared-influence inequality by $N$ preserves its direction, proving the lower bound.

**Key facts.** `FABL.fourierWeightAtLevel_one_majority_odd`, `FABL.oddMajorityInfluence_pos`, `FABL.oddMajorityInfluenceMain_le`, `FABL.oddMajorityInfluenceMain_sq`.

**Caveat.** The supplied formal statement proves only the level-one lower bound, not the broader exercise and theorem claims included in the informal statement.
