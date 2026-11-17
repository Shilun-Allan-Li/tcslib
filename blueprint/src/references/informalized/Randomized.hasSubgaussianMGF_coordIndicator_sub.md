<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ErrorReduction.lean :: Randomized.hasSubgaussianMGF_coordIndicator_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subgaussian Bound for a Centered Bernoulli Coordinate

**Claim.** For $0\leq p\leq1$, the coordinate indicator minus $p$ under the specified product Bernoulli measure has a subgaussian moment generating function with variance proxy $(1/2)^2$.

**Proof.** The coordinate indicator takes only the values $0$ and $1$. Thus its centered version $X=\mathbf{1}_{\{\omega_i=\mathrm{true}\}}-p$ lies between $-p$ and $1-p$. Its mean is zero: the coordinate indicator is integrable and has integral $p$ (Randomized.integrable_coordIndicator and Randomized.integral_coordIndicator), so subtracting the constant $p$ gives integral zero. The bounded, mean-zero subgaussian criterion for a random variable in an interval now applies: an interval of width $b-a$ yields variance proxy $((b-a)/2)^2$. Here $a=-p$ and $b=1-p$, so the width is exactly one, and the proxy is $(1/2)^2$. Measurability of the coordinate indicator, and hence of its centered version, is ensured by Randomized.measurable_coordIndicator.

**Key facts.** `Randomized.measurable_coordIndicator`, `Randomized.integrable_coordIndicator`, `Randomized.integral_coordIndicator`.
