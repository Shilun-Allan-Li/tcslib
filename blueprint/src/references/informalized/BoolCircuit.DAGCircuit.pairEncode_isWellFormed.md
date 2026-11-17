<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.DAGCircuit.pairEncode_isWellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair encoding preserves well-formedness

**Claim.** If every gate of $C$ has distinct input vertices, every NOT gate has exactly one input, and every gate has at most two inputs, then the circuit obtained by wiring to the pair encoding has distinct input vertices at each gate and exactly one input at every NOT gate.

**Proof.** The input-buffer structural theorem (`DAGCircuit.bufferInputs_structure`) states, in particular, that buffering the inputs of a fan-in-two circuit produces a well-formed circuit. The hypothesis says exactly that $C$ is fan-in two, and the pair-encoded circuit is $C$ buffered by `pairWiring n r`. Its well-formedness is therefore the desired conclusion.

**Key facts.** `BoolCircuit.DAGCircuit.bufferInputs_structure`.
