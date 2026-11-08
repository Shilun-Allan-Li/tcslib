<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yAfterSpecial_flipSpecialX -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance under flipping Alice’s special bit

**Claim.** Replacing Alice’s bit at the special coordinate by its negation leaves Bob’s post-special vector unchanged.

**Proof.** Compare the vectors at an arbitrary coordinate $i$. The flip leaves the special coordinate, Bob’s special bit, and every coordinate type unchanged. Hence Bob’s bit at $i$ is unchanged; the condition that $i$ lies strictly after the special coordinate is unchanged as well. The post-special vectors therefore agree at every coordinate, and so are equal.
