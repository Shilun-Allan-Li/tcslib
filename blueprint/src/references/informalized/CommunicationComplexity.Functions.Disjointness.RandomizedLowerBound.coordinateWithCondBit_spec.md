<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateWithCondBit_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional coordinate recovers its bit

**Claim.** The coordinate formed from a bit according to whether its index lies below the split point has that bit when read from Alice below the split and from Bob at or above it.

**Proof.** First consider $k<i$. If $b$ is false, the coordinate is neither and Alice’s bit is false; if $b$ is true, it is left-only and Alice’s bit is true. Thus Alice’s bit equals $b$. Now consider $k\not<i$, so $k\ge i$. If $b$ is false, the coordinate is neither and Bob’s bit is false; if $b$ is true, it is right-only and Bob’s bit is true. Thus Bob’s bit equals $b$, proving the stated piecewise equality.
