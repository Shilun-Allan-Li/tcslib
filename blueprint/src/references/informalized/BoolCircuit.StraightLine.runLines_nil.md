<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.runLines_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty Program Evaluation

**Claim.** For any natural number $n$ and Boolean assignment $x$ to the inputs, running the empty straight-line program on $x$ returns the empty list.

**Proof.** The execution is a left fold over the list of statements, starting from the empty list. Since there are no statements to process, the initial list is unchanged.
