<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean :: BooleanAnalysis.Hypercontractivity.noiseOp_affine_one_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise on an Affine One-Bit Function

**Claim.** For $f(x)=1+a\sigma(x)$ on the one-dimensional Boolean cube, the noise operator gives $(T_\rho f)(x)=1+\rho a\sigma(x)$.

**Proof.** The one-dimensional cube has two Fourier characters: the constant character and the sign character $\sigma$. The function $1+a\sigma$ has coefficients $1$ and $a$ on these characters. The noise operator multiplies the coefficient of a character by $\rho$ raised to its degree: the constant character has degree zero and the sign character degree one. Thus the resulting function is $1+\rho a\sigma(x)$ at each point.
