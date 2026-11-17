<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Basic.lean :: Expander.lambda_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the Spectral Parameter

**Claim.** The supremum $\lambda(A)$ of the norms $\|Av\|$ over unit vectors orthogonal to the uniform vector is nonnegative.

**Proof.** Every element of the set whose supremum defines $\lambda(A)$ is a norm, and hence is nonnegative. The supremum of a set of nonnegative real numbers is nonnegative, giving $0\le\lambda(A)$.
