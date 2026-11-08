<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.affine_pTwo_of_abs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine inequality from relative size

**Claim.** For $1\le p\le2$ and $|b|\le|a|$, the square root of $a^2+(p-1)b^2$ is at most the normalized $p$-mean of $|a+b|$ and $|a-b|$.

**Proof.** If $a=0$, the size assumption forces $b=0$, and both sides are zero. Otherwise set $e=b/a$, so $|e|\le1$. The normalized two-point inequality ($\texttt{normalized_pTwo_affine}$) gives $\sqrt{1+(p-1)e^2}\le\big(((1+e)^p+(1-e)^p)/2\big)^{1/p}$. Since $1\pm e\ge0$, factoring $a$ from $a+b$ and $a-b$ shows that their absolute values are $|a|(1+e)$ and $|a|(1-e)$. Also $a^2+(p-1)b^2=a^2(1+(p-1)e^2)$. Taking the indicated roots therefore multiplies both sides of the normalized inequality by $|a|$, yielding the claim.

**Key facts.** `FABL.normalized_pTwo_affine`.
