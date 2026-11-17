<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.completeQuadraticBoolean_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real form on the sign cube

**Claim.** For each $n$, the real-valued form of the sign-encoded complete quadratic Boolean function equals the complete quadratic function transported from the Boolean cube to the sign cube.

**Proof.** Fix a point of the sign cube. Evaluating the two functions there gives the same real number: on the left, the Boolean function applies the sign encoding to the complete quadratic bit at the inverse image of that point, then takes its real value; on the right, the complete quadratic function first sign-encodes that same bit and takes its real value. The definitions therefore agree pointwise, and hence the functions are equal.
