<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DisjointModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateOfBits_xBit_yBit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstructing a disjointness coordinate

**Claim.** For every disjointness coordinate, forming its two player-bits and then rebuilding the coordinate from those bits recovers the original coordinate.

**Proof.** There are three coordinate values. For neither, both bits are false, so rebuilding gives neither. For left-only, the bits are true and false, so rebuilding gives left-only. For right-only, the bits are false and true, so rebuilding gives right-only. Hence reconstruction returns the original coordinate in all cases.
