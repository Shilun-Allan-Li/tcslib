<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.inner_gaussianCorrelationMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner product of Gaussian correlation images

**Claim.** The inner product of the Gaussian correlation image of $(u,v)$ with a vector $t$ in the correlation plane is $u$ times the sum of the first coordinate of $t$ and $\rho$ times its second coordinate, plus $v$ times $\sqrt{1-\rho^2}$ times its second coordinate.

**Proof.** The Gaussian correlation image has coordinates $(u,\rho u+\sqrt{1-\rho^2}v)$. Pairing this with $t=(t_1,t_2)$ gives $ut_1+(ho u+\sqrt{1-\rho^2}v)t_2$. Distributing and regrouping yields $u(t_1+\rho t_2)+v\sqrt{1-\rho^2}t_2$, as claimed.
