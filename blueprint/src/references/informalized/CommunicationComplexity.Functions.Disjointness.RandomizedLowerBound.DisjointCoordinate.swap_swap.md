<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.DisjointCoordinate.swap_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Swap is an involution

**Claim.** Swapping the two sides of a disjoint coordinate twice returns the original coordinate.

**Proof.** Check the three possible states. The state neither is fixed by each swap. The state left only is sent to right only and then back to left only; conversely, right only is sent to left only and then back to right only. Thus the double swap equals the original state in every case.
