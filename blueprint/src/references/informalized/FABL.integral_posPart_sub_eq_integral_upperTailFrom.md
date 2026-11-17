<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integral_posPart_sub_eq_integral_upperTailFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive-Part Integral and Upper Tails

**Claim.** If $z\mapsto(z-t)^+$ is integrable with respect to $\nu$, then its integral equals the integral over $u>0$ of the real measure of $(t+u,\infty)$.

**Proof.** Apply the layer-cake formula to the nonnegative integrable function $z\mapsto(z-t)^+$, expressing its integral as the integral over positive levels $u$ of the measure of the set where $u<(z-t)^+$. For $u>0$, this set is exactly $(t+u,\infty)$ (\(\texttt{setOf\_lt\_posPart\_sub\_eq\_Ioi\_add}\)). Substituting this set identity into the layer-cake expression gives the asserted upper-tail integral.

**Key facts.** `FABL.setOf_lt_posPart_sub_eq_Ioi_add`.
