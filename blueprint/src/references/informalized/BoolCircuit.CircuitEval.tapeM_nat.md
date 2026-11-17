<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine.lean :: BoolCircuit.CircuitEval.tapeM_nat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Natural-index tape marks

**Claim.** For a finite list of natural numbers and a natural number j, the mark tape evaluated at the integer position corresponding to j equals the indicator of whether j belongs to the list.

**Proof.** Evaluate the tape at the integer cast of $j$. Since $j$ is nonnegative, the condition that this integer is nonnegative holds, and converting it back to a natural number gives $j$. Thus the tape’s defining condition reduces to $j$ belonging to the list: its value is `some true` exactly in that case and `none` otherwise. This is precisely the definition of the mark-cell indicator.
