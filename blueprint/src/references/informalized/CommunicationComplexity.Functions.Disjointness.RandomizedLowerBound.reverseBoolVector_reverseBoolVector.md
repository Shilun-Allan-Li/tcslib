<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.reverseBoolVector_reverseBoolVector -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reversal Is an Involution

**Claim.** Reversing the coordinate order of a Boolean vector twice returns the original vector.

**Proof.** To prove equality of the two vectors, compare their values at an arbitrary coordinate $i$. Reversal reads the coordinate at the reversed index; applying reversal again reads the coordinate at the reversal of that index. Since reversing an index in $\	ext{Fin }n$ twice returns the original index, the resulting value is exactly $v_i$. Thus the vectors agree at every coordinate.
