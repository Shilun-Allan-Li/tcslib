<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.LinesValid.nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of the Empty List

**Claim.** The empty list of straight-line statements is valid: every statement in it uses only inputs or earlier lines.

**Proof.** Validity requires checking the condition at every index less than the list's length. The empty list has no such indices, so the condition holds vacuously.
