<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.DAGCircuit.IsStrict.exists_fanoutTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded fan-out equivalent circuit

**Claim.** Every strict finite Boolean circuit with positive fan-out at every non-output vertex has a strict, equivalent circuit with the same number of inputs, fan-out at most two, and size at most twenty times the original size.

**Proof.** Apply the strict-circuit fan-out reduction theorem (`DAGCircuit.exists_isStrict_fanoutTwo_of_strict`) to $C$. Its hypothesis is exactly that every gate of $C$ is strict, which is the first part of the assumption that $C$ is strict. The theorem supplies a circuit $C'$ with the same number of inputs, strict gates, fan-out at most two, the same evaluation on every input, and the stated size bound. These are the required conclusions.

**Key facts.** `BoolCircuit.DAGCircuit.exists_isStrict_fanoutTwo_of_strict`.
