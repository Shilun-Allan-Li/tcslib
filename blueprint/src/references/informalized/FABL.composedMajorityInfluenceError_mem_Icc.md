<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.composedMajorityInfluenceError_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed Majority Influence Error Bounds

**Claim.** For every integer $m\ge 0$, the total influence of the composed majority on the sign cube of dimension $2+(2m+1)$, minus $1+\frac12\sqrt{2/\pi}\sqrt{2m+1}$, lies in $[0,\,1/(2\sqrt{2m+1})]$.

**Proof.** By the identity expressing the composed-majority influence error as one half of the odd-majority total influence error (`composedMajorityInfluenceError_eq`), it suffices to scale the known interval bound for the latter. The odd-majority error is nonnegative, so multiplying it by $1/2$ preserves nonnegativity. Its upper bound is $1/\sqrt{2m+1}$; multiplication by the nonnegative number $1/2$ preserves the inequality and gives $1/(2\sqrt{2m+1})$ after simplifying.

**Key facts.** `FABL.composedMajorityInfluenceError_eq`, `FABL.oddMajorityTotalInfluenceError_mem_Icc`.
