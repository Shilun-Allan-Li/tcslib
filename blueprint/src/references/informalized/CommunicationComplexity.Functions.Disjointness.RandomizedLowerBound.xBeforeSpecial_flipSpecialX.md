<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBeforeSpecial_flipSpecialX -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance of the Before-Special Prefix

**Claim.** Flipping Alice’s special bit leaves her padded before-special vector unchanged.

**Proof.** Evaluate the two vectors at an arbitrary coordinate $i$. If $i<T$, then $i\ne T$, so Alice’s bit there is read from the unchanged per-coordinate assignment; the flip changes only the special bit. If $i\not<T$, both vectors have value $\mathrm{false}$ by the padding in their definition. Thus the vectors agree at every coordinate.
