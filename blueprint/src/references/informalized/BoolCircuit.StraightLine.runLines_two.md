<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.StraightLine.runLines_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation After Two Appended Statements

**Claim.** Evaluating $ss$ followed by $s$ and $t$ gives the evaluation of $ss$ followed by the value of $s$ on that evaluation and the value of $t$ on the execution extended by the value of $s$.

**Proof.** Regroup the list as $(ss++[s])++[t]$. Apply the one-statement evaluation formula first to the final $t$, then to the preceding $s$. The result is the values from $ss$, followed by $s$ evaluated on those values, followed by $t$ evaluated on the list that already includes the value of $s$.

**Key facts.** `BoolCircuit.StraightLine.runLines_snoc`.
