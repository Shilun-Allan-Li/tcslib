<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: BooleanAnalysis.expect_eq_fintypeExpect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation as a finite average

**Claim.** For a real-valued function on the Boolean cube, the expectation defined using the uniform weight equals its finite uniform average over all points of the cube.

**Proof.** The uniform expectation on a finite type is the sum of the function's values divided by the cardinality of that type. The Boolean cube has $2^n$ elements, since it is the set of functions from an $n$-element coordinate set to a two-element set. Thus this average is $2^{-n}\sum_x f(x)$. By definition, the uniform weight is $2^{-n}$, so the defined expectation is the same quantity.
