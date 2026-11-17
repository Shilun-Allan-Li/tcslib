<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.one_sub_sqrt_le_two_div_pi_mul_arcsin_one_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Arcsine Lower Bound

**Claim.** For every real number $\delta$ with $0\leq\delta\leq1$, one has $1-\sqrt{\delta}\leq\frac{2}{\pi}\arcsin(1-\delta)$.

**Proof.** Set $t=\sqrt{\delta}$, so $0\leq t\leq1$ and $t^2=\delta$. Concavity of sine on $[0,\pi]$, applied between $0$ and $\pi/4$ with weights $1-t$ and $t$, gives $t\sqrt{2}/2\leq\sin(\pi t/4)$. Both sides are nonnegative, so squaring yields $\delta/2\leq\sin^2(\pi t/4)$. The double-angle identity then gives $\cos(\pi t/2)=1-2\sin^2(\pi t/4)\leq1-\delta$. Since $\pi t/2\in[0,\pi]$, the inverse cosine is decreasing on this range and $\arccos(\cos(\pi t/2))=\pi t/2$; hence $\arccos(1-\delta)\leq\pi t/2$. Finally, the arcsine–arccosine identity rewrites the desired right-hand side as $1-(2/\pi)\arccos(1-\delta)$ (`two_div_pi_mul_arcsin_eq_one_sub_two_div_pi_mul_arccos`). Substituting the bound on arccosine gives at least $1-t$, as required.

**Key facts.** `FABL.two_div_pi_mul_arcsin_eq_one_sub_two_div_pi_mul_arccos`.
