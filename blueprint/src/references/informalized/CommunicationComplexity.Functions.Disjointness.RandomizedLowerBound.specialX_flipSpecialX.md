<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialX_flipSpecialX -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipping Alice’s special bit

**Claim.** Toggling Alice’s special bit changes the special-$X$ value to its Boolean negation.

**Proof.** The flip leaves the special coordinate and all other data fixed, and replaces $x_T$ by its negation. The special-$X$ function reads $x_T$, so its value after the flip is exactly the negation of its value before the flip.
