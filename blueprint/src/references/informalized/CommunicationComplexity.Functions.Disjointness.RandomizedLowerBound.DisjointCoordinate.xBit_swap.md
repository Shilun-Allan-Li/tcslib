<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.DisjointCoordinate.xBit_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Swap exchanges the bits

**Claim.** For every disjoint coordinate, Alice's bit after swapping sides equals Bob's bit before the swap.

**Proof.** Check each state. For neither, the swap leaves the state unchanged and both bits are false. For left only, the swap produces right only, whose Alice bit is false, matching the original Bob bit. For right only, the swap produces left only, whose Alice bit is true, matching the original Bob bit.
