<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.DAGCircuit.exists_isStrict_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalent circuit representations

**Claim.** For a positive number of inputs, a Boolean function has a circuit with distinct gate arguments, at most two arguments per gate, and one argument at each NOT gate if and only if it has a circuit with strict gates and positive fanout at every nonoutput vertex.

**Proof.** For the forward implication, take a circuit computing the function with the stated fanin conditions. The strict conversion theorem gives an equivalent circuit that is strict and has positive fanout at every nonoutput vertex. Composing its evaluation equality with the original circuit's equality to the function proves that it computes the same function. For the reverse implication, a strict circuit is fanin two: strictness gives distinct arguments and the prescribed arity, which in particular implies the original fanin and NOT conditions. The circuit and its evaluation equality therefore already witness the required representation.

**Key facts.** `BoolCircuit.DAGCircuit.exists_isStrict`, `BoolCircuit.DAGCircuit.IsStrict.isFaninTwo`.
