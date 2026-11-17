<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.gaussianSourceDisagreement_polar -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polar characterization of Gaussian disagreement

**Claim.** For $\rho\in[-1,1]$ and a point $p=(r,\theta)$ in the target of the polar-coordinate map, the inverse image of $p$ lies in the Gaussian source disagreement set exactly when $\theta\in(-\pi,\pi)$ and $\cos\theta\cos(\theta-\arccos\rho)<0$.

**Proof.** First use $\cos(\arccos\rho)=\rho$ and $\sin(\arccos\rho)=\sqrt{1-\rho^2}$, valid for $\rho\in[-1,1]$. Substituting the polar-coordinate expression for the inverse image and expanding the cosine of a difference shows that the source disagreement expression equals $r^2\cos\theta\cos(\theta-\arccos\rho)$. Since $p$ lies in the polar-coordinate target, $r>0$, so $r^2>0$. Multiplication by this positive factor preserves the sign: the expression is negative exactly when the angular product is negative. The target condition also supplies $\theta\in(-\pi,\pi)$, giving precisely the stated angular characterization.
