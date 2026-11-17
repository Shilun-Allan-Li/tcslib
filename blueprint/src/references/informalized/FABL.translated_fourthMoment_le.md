<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveAnticoncentration.lean :: FABL.translated_fourthMoment_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Translated Fourth Moment Bound

**Claim.** If $X$ has mean zero, uniform $L^2$ norm $1$, and satisfies the stated hypercontractivity condition for $\rho>0$, then $\mathbb E[(X-\theta)^4]\leq((\rho^2)^{-1}+\theta^2)^2$.

**Proof.** Use hypercontractivity with input parameters $a=-\rho\theta$ and $b=1$. The resulting inequality compares the $L^4$ norm of $\rho(X-\theta)$ with the $L^2$ norm of $X-\rho\theta$. By homogeneity of the uniform norm (`uniformLpNorm_const_mul`) and positivity of $\rho$, this bounds $\rho\|X-\theta\|_4$ by $\|X-\rho\theta\|_2$. Raise both nonnegative sides to the fourth power. The fourth-power identity for the $L^4$ norm turns the left side into $\rho^4\mathbb E[(X-\theta)^4]$ (`uniformLpNorm_four_pow_eq_expect_fourth`). On the right, the mean-zero shift identity gives $\|X-\rho\theta\|_2^2=\|X\|_2^2+(\rho\theta)^2=1+(\rho\theta)^2$ (`uniformLpNorm_two_sub_const_sq`), so its fourth power is $(1+(\rho\theta)^2)^2$. Divide by the positive $\rho^4$ and simplify: $(1+(\rho\theta)^2)^2/\rho^4=((\rho^2)^{-1}+\theta^2)^2$.

**Key facts.** `FABL.uniformLpNorm_const_mul`, `FABL.uniformLpNorm_four_pow_eq_expect_fourth`, `FABL.uniformLpNorm_two_sub_const_sq`.
