<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: variance_scaled_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Scaled Rademacher Entry

**Claim.** For $k>0$, the random variable $(x_j/\sqrt{k})\omega_{ij}$ has variance $x_j^2/k$.

**Proof.** Variance scales quadratically: multiplying a random variable by $c$ multiplies its variance by $c^2$. Apply this with $c=x_j/\sqrt{k}$ and use that the unscaled entry has variance $1$ (variance_entry). Since $k>0$, $(\sqrt{k})^2=k$, so the resulting variance is $(x_j/\sqrt{k})^2=x_j^2/k$.

**Key facts.** `variance_entry`.
