<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.measureReal_specialBitsEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of Prescribed Special Bits

**Claim.** For any prescribed bits $b_x,b_y$, the event that the special bits equal $b_x,b_y$ has probability $1/4$ under the uniform hard-sample measure.

**Proof.** Express the event as the product restriction in which the special coordinate is unrestricted, the two special bits lie in the singletons $\{b_x\}$ and $\{b_y\}$, and the remaining coordinate labels are unrestricted. The hard-sample product-measure formula factors its mass into the four corresponding marginal masses (`hardSample_measureReal_fieldProduct`). The unrestricted coordinate and label factors each have mass $1$, while each prescribed bit has mass $1/2$ (`uniformFin_univ`, `uniformBool_singleton`, and `uniformDisjointCoordinateVector_univ`). Their product is $1\cdot\tfrac12\cdot\tfrac12\cdot1=\tfrac14$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.hardSample_measureReal_fieldProduct`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformFin_univ`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_singleton`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_univ`.
