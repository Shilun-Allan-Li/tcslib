<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialY_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bob’s Special Bit Is False with Probability One Half

**Claim.** Under the uniform law on hard samples, Bob’s bit at the special coordinate is false with probability $1/2$.

**Proof.** Express the event that the special bit of Bob is false as the product condition that the special coordinate is unrestricted, Alice’s special bit is unrestricted, Bob’s special bit lies in $\{\mathrm{false}\}$, and the other-coordinate vector is unrestricted. The product-measure formula for hard samples (`hardSample_measureReal_fieldProduct`) factors the probability into the four component probabilities. The unrestricted factors each have probability $1$ (`uniformFin_univ`, `uniformBool_univ`, and `uniformDisjointCoordinateVector_univ`), while the specified Boolean value has probability $1/2$ (`uniformBool_singleton`). Their product is $1/2$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.hardSample_measureReal_fieldProduct`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformFin_univ`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_univ`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_univ`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_singleton`.
