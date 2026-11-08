<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLine.lean :: BoolCircuit.SLOperand.eval_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Operand evaluation under list extension

**Claim.** If every line operand referenced by $o$ has index less than the length of $ys$, then evaluating $o$ on $ys$ appended with $ext$ gives the same value as evaluating it on $ys$.

**Proof.** Split by the operand. If it is a line operand with index $r$, the hypothesis says $r<|ys|$. A defaulted lookup at an index already within the original list is unchanged when a list is appended, so the two evaluations agree. For an input or negated-input operand, evaluation depends only on the assignment $x$, not on the value list, and hence is unchanged.
