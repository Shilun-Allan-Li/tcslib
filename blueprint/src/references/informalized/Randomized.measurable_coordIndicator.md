<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ErrorReduction.lean :: Randomized.measurable_coordIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of a Coordinate Indicator

**Claim.** For every natural number $k$ and coordinate $i\in\{0,\ldots,k-1\}$, the function on Boolean vectors of length $k$ that equals $1$ when coordinate $i$ is true and $0$ otherwise is measurable.

**Proof.** The coordinate projection sending a Boolean vector $\omega$ to its value at $i$ is measurable (`measurable_pi_apply i`). Every function from the discrete Boolean space to $\mathbb R$ is measurable, in particular the function sending true to $1$ and false to $0$. The coordinate indicator is the composition of this function with the coordinate projection, and compositions of measurable functions are measurable.
