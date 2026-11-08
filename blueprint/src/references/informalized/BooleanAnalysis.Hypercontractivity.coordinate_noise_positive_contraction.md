<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Contraction.lean :: BooleanAnalysis.Hypercontractivity.coordinate_noise_positive_contraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive coordinate-noise contraction

**Claim.** For $0\le\rho\le1$ and $q\ge1$, coordinate noise with parameter $\rho$ contracts the $q$-norm on every finite product space.

**Proof.** At each outcome, the noise value is the convex combination $\rho f+(1-\rho)Cf$, where $C$ is conditional expectation over the selected coordinate. The weighted absolute-power inequality for a probability distribution bounds its $q$th absolute power by $\rho|f|^q+(1-\rho)|Cf|^q$. Taking expectations preserves this inequality because each product mass is nonnegative. Conditional expectation does not increase the $q$th absolute moment for $q\ge1$, so the resulting upper bound is at most $\rho\mathbb E|f|^q+(1-\rho)\mathbb E|f|^q=\mathbb E|f|^q$. The moments are nonnegative; raising both sides to the nonnegative power $1/q$ gives the claimed norm contraction.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.weighted_abs_rpow_sum_le`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.condExp_moment_le`.
