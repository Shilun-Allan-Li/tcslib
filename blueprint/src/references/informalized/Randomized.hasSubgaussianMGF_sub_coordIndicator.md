<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ErrorReduction.lean :: Randomized.hasSubgaussianMGF_sub_coordIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subgaussian Bound for a Reversed Centered Bernoulli Coordinate

**Claim.** For $0\leq p\leq1$, $p$ minus the coordinate indicator has a subgaussian moment generating function with variance proxy $(1/2)^2$.

**Proof.** The previous centered-coordinate result gives the subgaussian bound for $X=\mathbf{1}_{\{\omega_i=\mathrm{true}\}}-p$. Negating a subgaussian random variable preserves the same variance proxy, so $-X=p-\mathbf{1}_{\{\omega_i=\mathrm{true}\}}$ has the required bound (Randomized.hasSubgaussianMGF_coordIndicator_sub). Pointwise, this identity is just rearrangement of the terms.

**Key facts.** `Randomized.hasSubgaussianMGF_coordIndicator_sub`.
