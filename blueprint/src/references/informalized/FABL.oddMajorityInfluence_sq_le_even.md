<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierWeightLimits.lean :: FABL.oddMajorityInfluence_sq_le_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even-index influence bound

**Claim.** For every $m>0$, the squared odd-majority influence satisfies $I_m^2\le \dfrac{2}{\pi(2m)}$.

**Proof.** Apply the odd-majority bound with the same $m$, obtaining $I_m^2\le \dfrac{2(2m+2)}{\pi(2m+1)^2}$. Because $m>0$, both $2m$ and $\pi(2m)$ are positive, so the desired comparison can be checked by cross-multiplication. After cancelling the positive factor $2/\pi$, it reduces to $2m(2m+2)\le(2m+1)^2$, which holds since the right side exceeds the left side by $1$.

**Key facts.** `FABL.oddMajorityInfluence_sq_le`.
