<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityTotalInfluenceError_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Majority Influence Error Bound

**Claim.** For every integer $m\ge 0$, the total influence error $E_m$ for majority on the sign cube of dimension $2m+1$ lies between $0$ and $1/\sqrt{2m+1}$.

**Proof.** Put $N=2m+1$, viewed as a positive real number. The total influence of odd-dimensional majority is $N$ times its one-coordinate influence (\texttt{totalInfluence\_majority\_odd\_eq\_mul\_oddMajorityInfluence}), and $N$ times the main approximation to that influence is exactly $\sqrt{2/\pi}\sqrt N$ (\texttt{oddArity\_mul\_oddMajorityInfluenceMain}). Thus $E_m=N(\mathrm{oddMajorityInfluence}(m)-\mathrm{oddMajorityInfluenceMain}(m))$. The main term is at most the actual influence (\texttt{oddMajorityInfluenceMain\_le}), so this difference, and hence $E_m$, is nonnegative. For the upper bound, the one-coordinate error is at most $\mathrm{oddMajorityInfluenceMain}(m)/N$ (\texttt{oddMajorityInfluenceError\_mem\_Icc}). Multiplying by $N$ gives $E_m\le \mathrm{oddMajorityInfluenceMain}(m)$; the latter is at most $1/\sqrt N$ (\texttt{oddMajorityInfluenceMain\_le\_inv\_sqrt}).

**Key facts.** `FABL.totalInfluence_majority_odd_eq_mul_oddMajorityInfluence`, `FABL.oddArity_mul_oddMajorityInfluenceMain`, `FABL.oddMajorityInfluenceMain_le`, `FABL.oddMajorityInfluenceError_mem_Icc`, `FABL.oddMajorityInfluenceMain_le_inv_sqrt`.
