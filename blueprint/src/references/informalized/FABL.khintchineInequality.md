<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.khintchineInequality -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Khintchine inequality for linear forms

**Claim.** For every $p\ge1$, the $L_p$ norm of a sign-cube linear form is bounded above and below by positive constant multiples of its $L_2$ norm.

**Proof.** Split into the cases $1\le p\le2$ and $p>2$. In the first case, the degree-one to degree-two estimate gives $\|L\|_2\le e^{2/p-1}\|L\|_p$, while monotonicity of the uniform norms gives $\|L\|_p\le\|L\|_2$ (`khintchine_of_le_two`). Choose $c=e^{-(2/p-1)}/2$ and $C=2$. These are positive with $c<C$, and weakening the lower bound by a factor of two yields the required inequalities. In the second case, monotonicity gives $\|L\|_2\le\|L\|_p$, and the degree-one upper estimate gives $\|L\|_p\le\sqrt{p-1}\,\|L\|_2$ (`khintchine_of_two_le`). Choose $c=1/2$ and $C=2\sqrt{p-1}$. Since $p>2$, this $C$ exceeds $c$; the lower estimate follows by weakening monotonicity, and the upper estimate follows by enlarging its constant. Thus in either range the required positive constants exist.

**Key facts.** `FABL.khintchine_of_le_two`, `FABL.khintchine_of_two_le`, `FABL.uniformLpNorm_nonneg`.
