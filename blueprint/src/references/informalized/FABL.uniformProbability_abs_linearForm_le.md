<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/TwoDivPi.lean :: FABL.uniformProbability_abs_linearForm_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small interval probability for a linear form

**Claim.** If the coefficients have squared sum $1$ and each has absolute value at most $\delta$, then for $t\ge 0$ the probability that the random sign linear form lies in $[-t,t]$ is at most $2t+2C\delta$, where $C$ is the third-moment Berry–Esseen constant.

**Proof.** Take the independent Rademacher summands $X_i(x)=a_i x_i$ under the uniform sign measure. They are measurable and square-integrable, have mean zero, and their variances sum to $1$ by the normalization of the coefficients. Since each sign is $\pm1$, the coefficient bound gives $|X_i(x)|\le\delta$ for every outcome. The bound on the sum of third absolute moments (\texttt{FABL.sum_integral_abs_cube_le_of_ae_abs_le}) therefore gives $\sum_i\mathbb E|X_i|^3\le\delta$. Apply the Berry–Esseen interval estimate (\texttt{FABL.exercise5_16_interval}) to the sum over $[-t,t]$: its probability differs from that of a standard Gaussian on this interval by at most $2C\sum_i\mathbb E|X_i|^3$. The sum of the Rademacher summands is the stated linear form (\texttt{FABL.sum_twoDivPiRademacherSummand}), and the event is exactly $|\sum_i a_i x_i|\le t$; uniform sign measure assigns this event the uniform probability in the claim (\texttt{FABL.twoDivPiUniformMeasure_real_event}). Finally, the standard Gaussian assigns $[-t,t]$ probability at most its interval length $2t$ (\texttt{FABL.gaussianReal_real_Icc_neg_le_two_mul}). Combining these bounds yields $2t+2C\delta$.

**Key facts.** `FABL.sum_integral_abs_cube_le_of_ae_abs_le`, `FABL.exercise5_16_interval`, `FABL.sum_twoDivPiRademacherSummand`, `FABL.twoDivPiUniformMeasure_real_event`, `FABL.gaussianReal_real_Icc_neg_le_two_mul`.
