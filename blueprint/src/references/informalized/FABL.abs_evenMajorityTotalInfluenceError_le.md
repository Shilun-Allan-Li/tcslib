<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EvenMajority.lean :: FABL.abs_evenMajorityTotalInfluenceError_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Majority Influence Error

**Claim.** For even dimension $2m+2$ and any majority function on that cube, the difference between its total influence and $\sqrt{2/\pi}\sqrt{2m+2}$ has absolute value at most $4/\sqrt{2m+2}$.

**Proof.** Put $N=2m+1$, $M=2m+2=N+1$, and $c=\sqrt{2/\pi}$. The even-majority influence identity expresses the total influence as $c\sqrt N+e$, where the odd-majority error satisfies $0\le e\le1/\sqrt N$ (`totalInfluence_evenMajority_eq_odd_main_add_error`, `oddMajorityTotalInfluenceError_mem_Icc`). The difference from $c\sqrt M$ is therefore $e-cd$, where $d=\sqrt M-\sqrt N$. Since $c\le1$, it suffices to bound $d$ by $1/\sqrt N$. Rationalizing gives $d=1/(\sqrt M+\sqrt N)\le1/\sqrt N$, so the absolute error is at most $2/\sqrt N$. Finally, $\sqrt M\le2\sqrt N$ because $M=N+1$ and $N\ge1$. Hence $2/\sqrt N\le4/\sqrt M$, as required.

**Key facts.** `FABL.oddMajorityTotalInfluenceError_mem_Icc`, `FABL.totalInfluence_evenMajority_eq_odd_main_add_error`.
