<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.uniformLpNorm_four_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling the Fourth Norm

**Claim.** For $c\ge 0$, the uniform $L^4$ norm of the function $x\mapsto c f(x)$ equals $c$ times the uniform $L^4$ norm of $f$.

**Proof.** Both sides are nonnegative. Their fourth powers are equal: the fourth-power identity expresses each as a uniform average (`FABL.uniformLpNorm_four_pow_eq_expect_fourth`), and $(cf(x))^4=c^4f(x)^4$, so the average for $cf$ is $c^4$ times the average for $f$. The fourth power of $c\|f\|_4$ is the same quantity. Since the fourth-power function is strictly increasing on nonnegative reals, equality of fourth powers gives equality of the norms.

**Key facts.** `FABL.uniformLpNorm_four_pow_eq_expect_fourth`, `FABL.uniformLpNorm_nonneg`.
