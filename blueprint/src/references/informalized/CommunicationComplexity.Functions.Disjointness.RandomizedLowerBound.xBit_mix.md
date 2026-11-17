<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBit_mix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alice’s Input Is Preserved by Mixing

**Claim.** If the samples share their special coordinate, agree on Alice’s before-special bits, and agree on Bob’s after-special bits, then Alice’s bit at every coordinate in the mixed sample equals her bit in $\omega_X$.

**Proof.** Fix a coordinate $i$. If $i=T$, the mixed sample uses $\omega_X$’s Alice special bit, so the equality follows directly. Otherwise, the mixing construction assigns the coordinate from Alice’s bit in $\omega_X$ and Bob’s bit in $\omega_Y$. These two bits cannot both be true: the no-overlap consequence of the shared conditioning data (`not_xBit_left_and_yBit_right_of_same_conditioning`) rules this out. Since $i\ne T$, Alice’s bit in $\omega_X$ is the Alice bit of its per-coordinate assignment (`xBit_of_ne_special`). For a pair of bits that are not both true, the coordinate constructed from them has Alice bit equal to the first bit (`coordinateOfBits_xBit`). Thus the mixed sample’s Alice bit equals $\omega_X$’s at $i$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.not_xBit_left_and_yBit_right_of_same_conditioning`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBit_of_ne_special`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateOfBits_xBit`.
