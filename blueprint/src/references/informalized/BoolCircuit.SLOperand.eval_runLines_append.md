<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.SLOperand.eval_runLines_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Operand evaluation after program extension

**Claim.** If the referenced line indices of an operand are less than the length of $ss$, then its value after running $ss$ with $ext$ appended equals its value after running $ss$.

**Proof.** Running the appended program extends the list of values produced by running $ss$: there is some list $e$ such that `runLines (ss ++ ext) x = runLines ss x ++ e` (`BoolCircuit.StraightLine.runLines_append`). The operand's before condition transfers to the length of the value list produced by $ss$—that list has length $|ss|$. Apply the fact that evaluating an operand whose line index is within the original list is unchanged by appending further values (`BoolCircuit.SLOperand.eval_append`). The resulting evaluations are equal.

**Key facts.** `BoolCircuit.StraightLine.runLines_append`, `BoolCircuit.SLOperand.eval_append`.
