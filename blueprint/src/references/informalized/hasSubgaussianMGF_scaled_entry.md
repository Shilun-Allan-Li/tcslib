<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: hasSubgaussianMGF_scaled_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaled Rademacher Entry

**Claim.** For $k>0$, scaling an entry of the joint Rademacher array by $x_j/\sqrt{k}$ gives a sub-Gaussian variable with variance proxy $x_j^2/k$.

**Proof.** The unscaled entry is sub-Gaussian with variance proxy $1$ by the entry bound. Scaling a sub-Gaussian variable by a real constant $c$ changes its variance proxy from $\sigma$ to $c^2\sigma$; take $c=x_j/\sqrt{k}$ and $\sigma=1$. Since $k>0$, $\sqrt{k}^{\,2}=k$, and hence $c^2=x_j^2/k$. This identifies the resulting proxy with the one stated.

**Key facts.** `hasSubgaussianMGF_entry`, `hasSubgaussianMGF_const_mul`.
