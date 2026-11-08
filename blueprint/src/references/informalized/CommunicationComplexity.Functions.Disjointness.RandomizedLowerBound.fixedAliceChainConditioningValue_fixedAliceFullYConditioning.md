<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.fixedAliceChainConditioningValue_fixedAliceFullYConditioning -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Chain conditioning recoding identity

**Claim.** Applying the chain-rule recoding to Alice's strict-prefix input and Bob's full input yields Bob's prefix together with Alice's prefix and Bob's suffix, each padded by false outside its specified range.

**Proof.** Evaluate the composition at an arbitrary sample and compare the resulting functions coordinate by coordinate. The first component reads Bob's full input below $i$ and is false elsewhere, so it is exactly Bob's padded prefix. In the second component, the first function reads Alice's prefix at indices below $i$ and is false elsewhere; the second reads Bob's full input at indices at least $i$ and is false elsewhere. These are precisely the two components of Alice's conditioning, so the ordered pairs agree.
