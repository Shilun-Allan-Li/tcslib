<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.criticalLog_lower -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Logarithm Lower Bound

**Claim.** For every positive integer $w$, $2^{-w}+\frac12(2^{-w})^2\le-\log(1-2^{-w})$.

**Proof.** Write $x=2^{-w}$. The half-interval bound gives $0<x\le1/2$ (`FABL.criticalInverse_mem_Ioc`), so $|x|<1$. For $|x|<1$, the logarithm has the convergent series $-\log(1-x)=\sum_{i=0}^{\infty}x^{i+1}/(i+1)$. Every term is nonnegative because $x>0$. Therefore the sum is at least its first two terms, $x+x^2/2$, which yields the stated inequality.

**Key facts.** `FABL.criticalInverse_mem_Ioc`.
