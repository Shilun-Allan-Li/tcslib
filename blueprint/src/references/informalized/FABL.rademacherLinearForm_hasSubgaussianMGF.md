<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.rademacherLinearForm_hasSubgaussianMGF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subgaussianity of a Rademacher linear form

**Claim.** If the coefficients satisfy $\sum_i a_i^2=1$, then the Rademacher linear form is subgaussian with parameter $1$ under the uniform measure on the sign cube.

**Proof.** For each coordinate $i$, the sign $x_i$ takes values $-1$ and $1$, and has mean zero under the uniform cube measure (`signValue_eq_neg_one_or_one`, `integral_signCoordinate_eq_zero`). A centered random variable bounded in $[-1,1]$ is subgaussian with parameter $1$; scaling it by $a_i$ gives parameter $a_i^2$. Thus each summand $a_i x_i$ is subgaussian with parameter $a_i^2$. The coordinate summands are jointly independent under the uniform product measure (`rademacherSummands_iIndep`), so the sum is subgaussian with parameter equal to the sum of the individual parameters. That sum is $\sum_i a_i^2=1$. Finally, the sum of the coordinate summands is the linear form itself (`sum_rademacherSummand`), proving the claim.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`, `FABL.integral_signCoordinate_eq_zero`, `FABL.rademacherSummands_iIndep`, `FABL.sum_rademacherSummand`.
