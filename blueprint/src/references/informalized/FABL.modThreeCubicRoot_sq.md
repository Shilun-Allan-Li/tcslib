<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThreeCubicRoot_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square of the Cubic Root

**Claim.** For $\zeta=\exp(2\pi i/3)$, one has $\zeta^2=-\frac12-\frac{\sqrt3}{2}i$.

**Proof.** Squaring the exponential gives $\zeta^2=\exp(4\pi i/3)$. Since $4ig/3\pi=\pi+\pi/3$, the addition formulas give $\cos(4\pi/3)=-\cos(\pi/3)=-1/2$ and $\sin(4\pi/3)=-\sin(\pi/3)=-\sqrt3/2$. Applying Euler's formula yields the stated value.
