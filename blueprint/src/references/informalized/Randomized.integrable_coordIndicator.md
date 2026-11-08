<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ErrorReduction.lean :: Randomized.integrable_coordIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Coordinate Indicator

**Claim.** For $p\in[0,1]$, a natural number $k$, and a coordinate $i<k$, the indicator of whether coordinate $i$ is true is integrable under the product measure on independent Bernoulli-$p$ bits.

**Proof.** The coordinate indicator is measurable (the coordinate measurability fact, `Randomized.measurable_coordIndicator`). At every Boolean vector its value is either $0$ or $1$, so it lies in the interval $[0,1]$. A measurable function bounded in this interval is integrable under any measure; applying this bounded-integrability criterion gives the result.

**Key facts.** `Randomized.measurable_coordIndicator`.
