<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean :: BoolCircuit.MultiDAGCircuit.length_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of Circuit Evaluation

**Claim.** For every input, the evaluation list of a multi-output circuit has the same length as its list of designated output vertices.

**Proof.** The evaluation list is obtained by mapping one value lookup over the designated output vertices. A map preserves the length of a list, so the two lengths agree.
