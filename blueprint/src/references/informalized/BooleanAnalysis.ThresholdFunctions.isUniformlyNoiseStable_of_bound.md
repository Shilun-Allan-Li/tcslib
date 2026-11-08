<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.isUniformlyNoiseStable_of_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Noise Stability from a Bound

**Claim.** Under the stated Boolean-valuedness, nonnegativity, vanishing-limit, and pointwise sensitivity-bound assumptions, the class is uniformly noise stable.

**Proof.** Keep the assumed bound $[0mε$ for small sensitivity and cap it at one: define $\eta(\delta)=\min\{1,\varepsilon(\delta)\}$. On $[0,1/2]$, both entries of this minimum are nonnegative, so $\eta$ is nonnegative, and it is at most one. The minimum of the constant function $1$ and $\varepsilon$ tends to zero as $\delta\to0^+$, because $\varepsilon$ does. For each class member and each $0<\delta\le1/2$, sensitivity is at most $1/2$ by the universal sensitivity bound (`noiseSensitivity_le_half`), and also at most $\varepsilon(\delta)$ by hypothesis. It is consequently at most their minimum, which is at most $\eta(\delta)$ by definition. Together with the assumed Boolean-valuedness, these properties establish uniform noise stability.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.noiseSensitivity_le_half`.
