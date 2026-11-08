<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ContinuousReasonableness.lean :: FABL.deriv_one_add_sq_mul_exp_half_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Gaussian exponential polynomial

**Claim.** For every real $t$, the derivative of $(1+t^2)e^{t^2/2}$ is $(3t+t^3)e^{t^2/2}$.

**Proof.** Fix $t$. Apply the product rule to $(1+t^2)e^{t^2/2}$, using the derivative formula for the Gaussian exponential ($\texttt{FABL.deriv\_exp\_half\_sq}$). The polynomial factor has derivative $2t$: this follows by differentiating the constant term and the square separately. Substituting these derivatives into the product rule and collecting terms gives $(2t+t(1+t^2))e^{t^2/2}=(3t+t^3)e^{t^2/2}$.

**Key facts.** `FABL.deriv_exp_half_sq`.
