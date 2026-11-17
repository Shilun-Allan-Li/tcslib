<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/BoolFourier.lean :: BoolFourier.expectation_eq_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Uniform Expectations

**Claim.** For every Boolean function on the $n$-dimensional Boolean cube, the expectation defined by dividing its sum by $2^n$ equals the expectation defined using the uniform weight.

**Proof.** Unfolding the two definitions, the first expectation is the sum of the function over the cube divided by $2^n$, while the second is that sum multiplied by $(2^{-1})^n$. The identity $(2^n)^{-1}=(2^{-1})^n$, followed by commutativity of multiplication, makes these expressions equal.
