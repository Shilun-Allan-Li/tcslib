<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DisjointModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBit_of_ne_special -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alice’s Bit Away from the Special Coordinate

**Claim.** At every coordinate $i\ne T$, Alice’s bit is the Alice bit of the per-coordinate assignment at $i$.

**Proof.** By definition, Alice’s bit at $i$ is the special bit only when $i=T$; otherwise it is read from the per-coordinate assignment. The hypothesis $i\ne T$ selects this latter case, proving the equality.
