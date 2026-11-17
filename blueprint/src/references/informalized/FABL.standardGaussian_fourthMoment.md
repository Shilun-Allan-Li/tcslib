<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ContinuousReasonableness.lean :: FABL.standardGaussian_fourthMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Moment of the Standard Gaussian

**Claim.** The fourth moment of the standard Gaussian measure is $3$: $\int_{\mathbb R}x^4\,d\gamma(x)=3$.

**Proof.** The fourth moment equals the fourth derivative at zero of the moment-generating function of the identity random variable, by the moment-generating-function derivative formula (`iteratedDeriv_mgf_zero`). For the standard Gaussian this moment-generating function is $\exp(t^2/2)$ (`mgf_fun_id_gaussianReal`). Differentiate successively: the first derivative is $t\exp(t^2/2)$, the second is $(1+t^2)\exp(t^2/2)$, the third is $(3t+t^3)\exp(t^2/2)$, and the fourth is $(3+6t^2+t^4)\exp(t^2/2)$. At $t=0$ this is $3$.

**Key facts.** `FABL.deriv_exp_half_sq`, `FABL.deriv_t_mul_exp_half_sq`, `FABL.deriv_one_add_sq_mul_exp_half_sq`, `FABL.deriv_three_mul_add_cube_mul_exp_half_sq`.
