<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.reverseSet_reverseSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involution on Subsets

**Claim.** For every subset $S$ of the coordinates, reversing its coordinates twice returns $S$.

**Proof.** Fix a coordinate $i$. Membership of $i$ in the twice-reversed set means that reversing $i$ gives an element of the once-reversed set; this in turn means reversing that coordinate gives an element of $S$. Reversal of coordinates is an involution, so the twice-reversed coordinate is $i$. Hence $i$ belongs to the twice-reversed set exactly when it belongs to $S$, proving equality of the sets.
