<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_fixedAliceCrossInfoTriple_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniformity of Alice's Information Triple

**Claim.** Under disjointness conditioning, the triple formed from Alice's bit at $i$, Bob's bits before $i$, and the fixed-coordinate conditioning data has the same law as the corresponding triple formed from a uniformly drawn disjoint-coordinate vector.

**Proof.** First, each of the three components of the sample-based triple agrees almost everywhere, under the disjointness-conditioned measure, with the corresponding component obtained from the generated disjoint-coordinate vector: this holds for Alice's fixed bit (\texttt{fixedXBit\_ae\_eq\_coordinateXBit}), Bob's bits before $i$ (\texttt{fixedYBefore\_ae\_eq\_coordinateYBefore}), and the conditioning data (\texttt{fixedAliceConditioning\_ae\_eq\_coordinateAliceConditioning}). Hence the triples themselves agree almost everywhere, and almost-everywhere equal random variables have the same distribution. Finally, the generated coordinate vector is uniformly distributed under disjointness conditioning (\texttt{identDistrib\_disjointCoordinateVector\_uniform}); applying the map that forms the coordinate-based triple preserves identical distribution. Chaining these two distributional equalities proves the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.fixedXBit_ae_eq_coordinateXBit`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.fixedYBefore_ae_eq_coordinateYBefore`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.fixedAliceConditioning_ae_eq_coordinateAliceConditioning`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_disjointCoordinateVector_uniform`.
