<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.runWith_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of an Empty Gate List

**Claim.** Evaluating an empty gate list from an initial output list returns that initial list.

**Proof.** The empty list is the identity case of the defining fold: no gate appends an output, so the list remains $init$.
