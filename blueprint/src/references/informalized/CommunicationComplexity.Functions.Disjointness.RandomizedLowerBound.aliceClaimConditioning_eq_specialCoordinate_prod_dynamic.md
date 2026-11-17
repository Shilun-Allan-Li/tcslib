<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.aliceClaimConditioning_eq_specialCoordinate_prod_dynamic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditioning as Coordinate and Dynamic Data

**Claim.** Alice’s corrected conditioning function is the function that pairs the special coordinate with Alice’s corrected dynamic conditioning data.

**Proof.** At each sample, Alice’s corrected conditioning is the ordered triple consisting of the special coordinate, Alice’s prefix vector, and Bob’s suffix vector. Alice’s dynamic conditioning is exactly the ordered pair of those two vectors. Pairing the special coordinate with that pair gives the same nested product value, so the functions agree by their definitions.
