<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.exists_nonnegative_correlation_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting a Nonnegative Correlation

**Claim.** For $r,s\in[0,1]$ and $0\le\rho\le\sqrt{rs}$, there are $a,b$ with $0\le a\le\sqrt r$, $0\le b\le\sqrt s$, and $ab=\rho$.

**Proof.** If $r=0$, then $\sqrt{rs}=0$, so the bounds on $\rho$ force $\rho=0$. Choose $a=b=0$; these satisfy the required bounds and product identity. If $r\ne0$, the assumption $r\ge0$ gives $r>0$, hence $\sqrt r>0$. Set $a=\sqrt r$ and $b=\rho/\sqrt r$. These choices give the bounds on $a$ and $b\ge0$. Dividing the assumed inequality $\rho\le\sqrt{rs}=\sqrt r\sqrt s$ by the positive number $\sqrt r$ gives $b\le\sqrt s$. Finally, $ab=\sqrt r(\rho/\sqrt r)=\rho$.
