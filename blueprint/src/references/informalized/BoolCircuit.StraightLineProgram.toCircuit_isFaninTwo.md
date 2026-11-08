<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLineProgram.toCircuit_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-In of the Translated Circuit

**Claim.** Every gate in the translated circuit has at most two distinct input vertices, and each negation gate has exactly one input vertex.

**Proof.** Consider an arbitrary gate in the translated circuit and classify it by its source in the construction. A gate among those generated for input negations has one input vertex, so its arguments are distinct and its fan-in is at most two. A gate generated from a straight-line statement has at most two arguments, one for each operand; the translation's cases for conjunction and disjunction also ensure that any negation gate in this group has exactly one argument. The remaining possible gate is the constant gate, whose arguments satisfy the same requirements. Thus every gate has distinct arguments, every negation gate has exactly one argument, and every gate has fan-in at most two. These are exactly the two conditions defining the claimed circuit property.
