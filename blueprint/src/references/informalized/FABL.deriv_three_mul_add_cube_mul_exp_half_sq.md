<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ContinuousReasonableness.lean :: FABL.deriv_three_mul_add_cube_mul_exp_half_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a cubic Gaussian exponential function

**Claim.** For every real $t$, the derivative of $(3t+t^3)e^{t^2/2}$ is $(3+6t^2+t^4)e^{t^2/2}$.

**Proof.** Fix $t$ and use the product rule. The derivative of the Gaussian exponential is $t e^{t^2/2}$ by the Gaussian exponential derivative formula ($\texttt{FABL.deriv\_exp\_half\_sq}$). The polynomial factor has derivative $3+3t^2$, obtained by differentiating its linear and cubic terms. Thus the derivative is $\bigl(3+3t^2+t(3t+t^3)\bigr)e^{t^2/2}$, which simplifies to $(3+6t^2+t^4)e^{t^2/2}$.

**Key facts.** `FABL.deriv_exp_half_sq`.
