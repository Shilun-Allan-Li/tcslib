<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.criticalLog_upper -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Logarithm Upper Bound

**Claim.** For every positive integer $w$, $-\log(1-2^{-w})\le\frac{2^{-w}}{1-2^{-w}}$.

**Proof.** Let $x=2^{-w}$ and $q=1-x$. The critical base bound gives $0<q<1$ (`FABL.criticalBase_mem_Ioo`). Apply $\log y\le y-1$ to $y=1/q>0$. Using $\log(1/q)=-\log q$ and rearranging gives $-\log q\le q^{-1}-1$. Since $q=1-x$, the right side simplifies to $x/(1-x)$, proving the bound.

**Key facts.** `FABL.criticalBase_mem_Ioo`.
