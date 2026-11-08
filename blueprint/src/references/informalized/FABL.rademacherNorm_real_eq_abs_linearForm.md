<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdLevelOne.lean :: FABL.rademacherNorm_real_eq_abs_linearForm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scalar Rademacher norm identity

**Claim.** For a real coefficient vector $a$ and sign vector $x$, the Rademacher norm of $a$ at $x$ equals the absolute value of the associated linear form.

**Proof.** In the real normed space $[31m\mathbb R[0m$, scalar multiplication satisfies $x_i\,a_i=a_i x_i$. Hence the vector sum inside the norm is exactly the scalar linear form $[31m\sum_i a_i x_i[0m$. The norm on the reals is absolute value, so its norm is $\left|\sum_i a_i x_i\right|$.
