<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityInfluenceError_le_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Power Bound for the Influence Error

**Claim.** For every natural number $m$, the majority influence error is at most $(2m+1)^{-3/2}$.

**Proof.** Put $N=2m+1$, which is positive. The error bound in `oddMajorityInfluenceError_mem_Icc` gives $\operatorname{Error}(m)\le \operatorname{Main}(m)/N$. By `oddMajorityInfluenceMain_le_inv_sqrt`, the main term is at most $1/\sqrt N$, so the error is at most $1/(N\sqrt N)$. The identity `oddArity_rpow_neg_three_halves` identifies this last quantity with $N^{-3/2}$, giving the claimed bound.

**Key facts.** `FABL.oddMajorityInfluenceError_mem_Icc`, `FABL.oddMajorityInfluenceMain_le_inv_sqrt`, `FABL.oddArity_rpow_neg_three_halves`.
