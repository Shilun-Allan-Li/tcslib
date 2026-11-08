<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityInfluence_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd majority influence recurrence

**Claim.** For every $m\ge0$, the influences satisfy $I_{m+1}=\dfrac{2m+1}{2m+2}I_m$.

**Proof.** The central-binomial recurrence says $(m+1)\binom{2m+2}{m+1}=2(2m+1)\binom{2m}{m}$. Substitute this into the defining expressions for $I_{m+1}$ and $I_m$. The denominator power satisfies $2^{2(m+1)}=4\cdot 2^{2m}$; combining this with the binomial recurrence and cancelling the positive factors gives $I_{m+1}=\frac{2m+1}{2m+2}I_m$.
