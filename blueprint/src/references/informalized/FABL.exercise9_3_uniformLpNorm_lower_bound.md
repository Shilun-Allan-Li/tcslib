<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.exercise9_3_uniformLpNorm_lower_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform norm lower bound

**Claim.** If $6d\le n$, then the fourth norm of the level-$3d$ polynomial is at least the fourth root of the multinomial-to-binomial ratio times its second norm.

**Proof.** Write $A=M(n,d)/\binom{n}{3d}^2$. The fourth-moment lower bound states that $A(\mathbb E F^2)^2\le \mathbb E F^4$ (`exercise9_3_fourthMoment_lower_bound`). The identities relating the uniform second and fourth norms to these moments (`uniformLpNorm_two_sq_eq_expect_sq` and `uniformLpNorm_even_pow_eq_expect_even`) turn this into $A\|F\|_2^4\le\|F\|_4^4$. Since both norms are nonnegative and $A\ge0$, taking fourth roots preserves the inequality. Equivalently, raise the desired inequality to the fourth power; the fourth power of $A^{1/4}$ is $A$, by the real-power laws for nonnegative $A$.

**Key facts.** `FABL.exercise9_3_fourthMoment_lower_bound`, `FABL.uniformLpNorm_two_sq_eq_expect_sq`, `FABL.uniformLpNorm_even_pow_eq_expect_even`, `FABL.uniformLpNorm_nonneg`.
