<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialCoordinate_preimage_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preimage of a Special Coordinate

**Claim.** The preimage of the singleton containing $i$ under the special-coordinate map is exactly the event that the sample's special coordinate equals $i$.

**Proof.** A sample belongs to the preimage precisely when its special coordinate belongs to the singleton $\{i\}$, which is equivalent to its special coordinate equaling $i$. By definition, this is precisely membership in the special-coordinate event. Since the two sets have the same members, they are equal.
