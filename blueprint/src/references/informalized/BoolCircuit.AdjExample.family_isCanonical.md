<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformExample.lean :: BoolCircuit.AdjExample.family_isCanonical -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical form of the example family

**Claim.** At every input length, the example family’s gate argument lists are strictly increasing, and its output index is one less than the total number of input and gate vertices.

**Proof.** Fix an input length and unfold the family and its constant circuit. The gate list is the fixed list used in that construction; its argument list is sorted in increasing order, as required. The output index and circuit size are given by the same construction, and simplifying these expressions gives output index plus one equal to the size. These are the two conditions defining canonical form.
