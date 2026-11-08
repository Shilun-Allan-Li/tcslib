<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SharpLevelOneInequality.lean :: FABL.sharpLevelOneInequality -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp level-one Fourier bound

**Claim.** If $f$ takes values in $[0,1]$ and has mean $\alpha>0$, then its level-one Fourier weight is at most $2\alpha^2\ln(1/\alpha)$.

**Proof.** Set $a_i=\widehat f(\{i\})$, $W=\sum_i a_i^2$, and normalize $q=f/\alpha$. Then $q\ge0$, its mean is $1$, and $q\le1/\alpha$. The entropy bound for a nonnegative mean-one function bounded by $M$ gives $\mathbb E[q\ln q]\le\ln M$; applying it with $M=1/\alpha$ yields $\mathbb E[q\ln q]\le\ln(1/\alpha)$. The entropy variational inequality says that for any real function $y$, $\mathbb E[qy]-\ln\mathbb E[e^y]\le\mathbb E[q\ln q]$. Choose $y$ to be the linear form with coefficients $a_i/\alpha$. Orthogonality of the cube characters gives $\mathbb E[qy]=W/\alpha^2$. The subgaussian moment bound for a Rademacher linear form gives $\mathbb E[e^y]\le\exp(W/(2\alpha^2))$, hence $\ln\mathbb E[e^y]\le W/(2\alpha^2)$. Combining these inequalities gives $W/\alpha^2-W/(2\alpha^2)\le\ln(1/\alpha)$, so $W\le2\alpha^2\ln(1/\alpha)$. Finally, the level-one weight is precisely the sum of the squared singleton coefficients, so this is the claimed bound.

**Key facts.** `FABL.expect_mul_log_le_log_bound`, `FABL.expect_mul_sub_log_expect_exp_le_entropy`, `FABL.expect_mul_linearForm_eq_singletonCoeffs`, `FABL.expect_exp_linearForm_le`, `FABL.fourierWeightAtLevel_one_eq_sum_singleton`.
