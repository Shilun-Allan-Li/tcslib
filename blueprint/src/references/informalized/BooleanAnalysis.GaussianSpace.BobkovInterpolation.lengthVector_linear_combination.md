<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Tensorization.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.lengthVector_linear_combination -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of the combined vector

**Claim.** The combined vector associated with the linear combinations of two functions and their auxiliary tuples is the same linear combination of the two corresponding combined vectors.

**Proof.** Since the claimed vectors have the same coordinates if they agree at every index, fix an index in the concatenated coordinate set. A coordinate is either one of the first $n$ derivative coordinates or one of the $m$ auxiliary coordinates. In the first case, the derivative of a linear combination is the same linear combination of the derivatives (`derivative_linear_combination`). In the second case, the coordinate is the corresponding auxiliary function value, and linearity follows directly from its definition. Thus every coordinate agrees.

**Key facts.** `BooleanAnalysis.GaussianSpace.derivative_linear_combination`.
