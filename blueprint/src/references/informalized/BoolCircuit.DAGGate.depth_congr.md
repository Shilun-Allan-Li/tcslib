<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.DAGGate.depth_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth depends on referenced values

**Claim.** If two lists of natural numbers give equal values, with out-of-range indices interpreted as zero, at every argument of a gate, then the gate's depth computed from the two lists is equal.

**Proof.** The depth is one plus the maximum, with initial value zero, of the looked-up values at the gate's arguments. The hypothesis gives equality of the looked-up values at each argument, so the two mapped lists agree term by term. Their maxima, and thus the resulting depths, are equal.
