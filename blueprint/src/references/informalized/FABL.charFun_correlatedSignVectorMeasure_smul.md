<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.charFun_correlatedSignVectorMeasure_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling a correlated sign-vector characteristic function

**Claim.** For $\rho\in[-1,1]$, $a\in\mathbb R$, and $t\in\mathbb R^2$, the characteristic function of the correlated sign-vector measure at $at$ equals the characteristic function at $a$ of the real projection $s_1t_1+s_2t_2$ under the correlated sign-pair distribution.

**Proof.** Write each characteristic function as the integral of the complex exponential against its measure. Because the sign-vector measure is the image of the correlated sign-pair distribution, the integral for the left side becomes an integral over sign pairs. The inner product of the sign vector with $t$ equals the real projection $s_1t_1+s_2t_2$ (FABL.correlatedSignProjection_eq_inner), and scaling $t$ by $a$ scales this projection by $a$ (FABL.correlatedSignProjection_smul). Thus the integrands agree pointwise with those defining the characteristic function of the projected distribution at $a$, proving equality of the integrals.

**Key facts.** `FABL.correlatedSignProjection_eq_inner`, `FABL.correlatedSignProjection_smul`.
