<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateAliceConditioning_eq_recode_condBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recoding Alice’s conditioning

**Claim.** Alice’s fixed-coordinate conditioning equals the result of forming its single conditioning bit-string and recoding that string into the padded pair of vectors.

**Proof.** Fix a coordinate assignment and compare the two pairs coordinate by coordinate. In the first component, if $j<i$, the recoded bit is the conditioning bit at $j$, which is Alice’s bit there; if $j\not<i$, both constructions give false. In the second component, if $i\le j$, the recoded bit is the conditioning bit at $j$, which is Bob’s bit there; if $i\not\le j$, both constructions give false. These cases establish equality of both component functions, hence of the pairs.
