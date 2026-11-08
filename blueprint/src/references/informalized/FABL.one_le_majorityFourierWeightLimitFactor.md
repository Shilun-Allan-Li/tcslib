<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierWeightLimits.lean :: FABL.one_le_majorityFourierWeightLimitFactor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Influence Factor Bound

**Claim.** For natural numbers $m$ and $j$ with $j\le m$, the majority influence factors satisfy $1\le (\pi/2)(2m+1)I(m-j)I(m)$.

**Proof.** Set $N=2m+1$ and $M=2(m-j)+1$. Since $j\le m$, we have $0<M\le N$. Replace each influence factor temporarily by its lower bound given by the square-root quantity `oddMajorityInfluenceMain`. Their product, multiplied by $(\pi/2)N$, is nonnegative. By the square identity for that quantity (`oddMajorityInfluenceMain_sq`), the square of this product is $N/M$. As $N\ge M>0$, this square is at least $1$, so the nonnegative product is at least $1$. Finally, each square-root quantity is at most the corresponding influence (`oddMajorityInfluenceMain_le`); multiplying these inequalities is valid because the factors are nonnegative, and gives the claimed bound.

**Key facts.** `FABL.oddMajorityInfluenceMain_sq`, `FABL.oddMajorityInfluenceMain_le`, `FABL.oddMajorityInfluence_pos`.
