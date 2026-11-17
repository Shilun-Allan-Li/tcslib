<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThreeCubicRoot_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cartesian Form of the Cubic Root

**Claim.** For $\zeta=\exp(2\pi i/3)$, one has $\zeta=-\frac12+\frac{\sqrt3}{2}i$.

**Proof.** Use $2\pi/3=\pi-\u03c0/3$ and the identities $\cos(\pi-t)=-\cos t$ and $\sin(\pi-t)=\sin t$ to write $\cos(2\pi/3)=-\cos(\pi/3)=-1/2$ and $\sin(2\pi/3)=\sin(\pi/3)=\sqrt3/2$. Euler's formula $\exp(i\theta)=\cos\theta+i\sin\theta$ then gives the claimed Cartesian form.
