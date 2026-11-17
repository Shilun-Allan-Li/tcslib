<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedKKL.lean :: FABL.eventually_exercise9_30_numeric_conditions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Eventual numerical conditions

**Claim.** For all sufficiently large natural numbers $n$, the three stated inequalities involving $\log n$, its powers, and an exponential of its square root hold.

**Proof.** As $n\to\infty$, $\log n\to\infty$, and therefore both $\sqrt{\log n}$ and $(\log n)^{1/12}$ tend to infinity. Also, with $x=\sqrt{\log n}/2$, one has $x\to\infty$ and $x^2=o(e^x)$; hence eventually $x^2\le e^x/2$. For sufficiently large $n$, we also have $(\log n)^{1/12}\ge96$ and $\log n>1$. Since $\log n>0$, multiplying the first of these bounds by $(\log n)^{5/12}$ gives $96(\log n)^{5/12}\le(\log n)^{1/2}=\sqrt{\log n}$. Finally, $x^2=\log n/4$, so $x^2\le e^x/2$ implies $\log n/2\le e^x$, the required exponential inequality.
