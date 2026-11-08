<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.rootOfUnity_pow_k -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A root of unity has the expected power

**Claim.** For positive $k$, the $k$-th power of $\omega_k=e^{2\pi i/k}$ is $1$.

**Proof.** The root $\omega_k$ is a primitive $k$-th root of unity, by the defining property of the complex root of unity used here (`isPrimitiveRoot_rootOfUnity`). A primitive $k$-th root has $k$-th power equal to $1`; applying this property gives the claim.

**Key facts.** `ZkFourier.isPrimitiveRoot_rootOfUnity`.
