<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/TVDistance.lean :: CommunicationComplexity.TVDistance.measureReal_sub_eq_sum_indicator_singletonMassDiff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton expansion of a measure gap

**Claim.** On a finite discrete measurable space, the difference $\mu(S)-\nu(S)$ is the sum over points of $\Omega$ of the singleton mass difference, with only points in $S$ contributing.

**Proof.** For each of the finite measures $\mu$ and $\nu$, its mass on $S$ is the sum of its singleton masses over points belonging to $S$ (`FiniteMeasureSpace.measureReal_eq_sum_singletons`). Subtract the two finite sums term by term. For each point, the resulting term is exactly the singleton mass difference when the point lies in $S$, and is zero otherwise. Summing these terms gives the claimed formula.

**Key facts.** `CommunicationComplexity.FiniteMeasureSpace.measureReal_eq_sum_singletons`.
