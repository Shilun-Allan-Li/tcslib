<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.isPrimitiveRoot_rootOfUnity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitivity of the Root of Unity

**Claim.** For positive $k$, the complex number $\omega_k=e^{2\pi i/k}$ is a primitive $k$-th root of unity: its $k$-th power is $1$, and its powers equal $1$ exactly at exponents divisible by $k$.

**Proof.** Apply the complex-exponential theorem stating that $e^{2\pi i/k}$ is a primitive $k$-th root of unity when $k$ is nonzero (`Complex.isPrimitiveRoot_exp`). Primitivity supplies both the fact that the $k$-th power is $1$ and the characterization of exponents whose powers equal $1.
