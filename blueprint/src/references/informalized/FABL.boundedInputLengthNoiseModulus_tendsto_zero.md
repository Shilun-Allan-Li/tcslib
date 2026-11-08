<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.boundedInputLengthNoiseModulus_tendsto_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing Noise Modulus

**Claim.** For every natural number $N$, the bounded input length noise modulus tends to zero as the parameter approaches zero through positive values in the half interval.

**Proof.** On the half interval, the modulus is the restriction of the function $\delta\mapsto\min(1,N\delta)$. This function is continuous: it is the minimum of the constant function $1$ and the product of the constant $N$ with the continuous coordinate function. Continuity at the zero parameter gives convergence to its value there, namely $\min(1,N\cdot0)=0$. Restricting the approach to positive parameters preserves this limit, since the neighborhood filter within the positive set is finer than the unrestricted neighborhood filter. The definition of the modulus then identifies this limit with the claimed one.
