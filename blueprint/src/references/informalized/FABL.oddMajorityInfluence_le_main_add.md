<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityInfluence_le_main_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An Upper Bound for Majority Influence

**Claim.** For every natural number $m$, the majority influence is at most the main term plus the main term divided by $2m+1$.

**Proof.** Set $N=2m+1>0$. Both the influence and the proposed upper bound are nonnegative, so it suffices to compare squares. The squared influence is at most $2(N+1)/(\pi N^2)$ by `oddMajorityInfluence_sq_le`. The square of the proposed bound can be written as the square of the main term times $(1+1/N)^2$. Using `oddMajorityInfluenceMain_sq`, this is $2/(\pi N)\,(1+1/N)^2$, which is at least $2(N+1)/(\pi N^2)$ because $(1+1/N)^2\ge 1+1/N$. Thus the squared quantities are ordered as required, and nonnegativity gives the claimed bound.

**Key facts.** `FABL.oddMajorityInfluence_pos`, `FABL.oddMajorityInfluence_sq_le`, `FABL.oddMajorityInfluenceMain_sq`.
