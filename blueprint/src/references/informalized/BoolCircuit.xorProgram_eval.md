<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.xorProgram_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the XOR program

**Claim.** For every assignment $x$ of Boolean values to two variables, the XOR program evaluates to true exactly when the two assigned values differ.

**Proof.** Expanding the program's evaluation follows its three straight-line instructions and reduces the claim to a Boolean calculation on the two input values. There are four assignments: when both values are false or both are true, the program evaluates to false; when exactly one is true, it evaluates to true. These are precisely the cases in which the two values differ.
