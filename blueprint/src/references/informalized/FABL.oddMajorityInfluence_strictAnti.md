<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityInfluence_strictAnti -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict decrease of odd majority influence

**Claim.** If $m<k$ are nonnegative integers, then $I_m>I_k$.

**Proof.** It suffices to show that each successive term is strictly smaller than its predecessor. The recurrence $I_{m+1}=\frac{2m+1}{2m+2}I_m$ (`oddMajorityInfluence_succ`) expresses the ratio as a factor strictly below $1$, since $2m+1<2m+2$. Also $I_m>0$ (`oddMajorityInfluence_pos`), so multiplying by this factor gives $I_{m+1}<I_m$. Strict decrease on the natural numbers follows by iterating this successive inequality from $m$ to $k$.

**Key facts.** `FABL.oddMajorityInfluence_succ`, `FABL.oddMajorityInfluence_pos`.
