<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseOperator.lean :: FABL.arccos_one_sub_two_mul_eq_two_mul_arcsin_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Arccosine–Arcsine Identity

**Claim.** For every $\delta\in[0,1]$, $\arccos(1-2\delta)=2\arcsin(\sqrt{\delta})$.

**Proof.** Because $0\le\delta\le1$, its square root lies in $[0,1]$, and the sine of its arcsine is therefore $\sqrt\delta$. Substitute this into $1-2\delta$ and use $\delta=(\sqrt\delta)^2$ to write that quantity as $1-2\sin^2(\arcsin\sqrt\delta)=\cos(2\arcsin\sqrt\delta)$, by the double-angle identity. Finally, $2\arcsin(\sqrt\delta)$ lies in $[0,\pi]$: the arcsine is nonnegative here and at most $\pi/2$. On this interval, applying arccosine to the cosine returns the angle itself, proving the identity.
