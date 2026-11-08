<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLine.LinesValid.snoc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity After Appending a Statement

**Claim.** If a valid list of straight-line statements is extended by a statement whose operands use only inputs or lines earlier than the old list's length, the extended list remains valid.

**Proof.** Consider any index in the appended list. It is either strictly below the old list's length, in which case the indexed statement is unchanged and is valid by the original hypothesis, or it is the new final index, in which case the required condition is exactly the assumed validity of the appended statement. Thus every index in the extended list satisfies the validity condition.
