<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.StraightLineProgram.eval_of_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation with No Inputs

**Claim.** If a straight-line program has zero input variables, then its evaluation at the unique assignment to those variables is false.

**Proof.** First show that the program has no statements. If its statement list were nonempty, validity at index zero would imply that the first statement's left operand can be read before line zero. An input or negated input operand would require an element of the empty type of input indices, while a line operand would require a natural number strictly less than zero. Each possibility is impossible. Thus the statement list is empty, and the definition of evaluation returns its default value, false.
