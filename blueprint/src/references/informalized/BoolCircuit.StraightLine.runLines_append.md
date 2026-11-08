<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.StraightLine.runLines_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending Statements to an Evaluation

**Claim.** Evaluating a list of statements followed by an extension gives the evaluation of the original list followed by some list of additional values.

**Proof.** Induct on the extension by appending its final statement. For an empty extension, choose the empty list of additional values. For an extension ending in a statement $s$, the induction hypothesis writes the evaluation of the earlier extension as the original evaluation followed by some list $e$. Appending $s$ appends its value evaluated on that earlier run (`runLines_snoc`). Thus the full evaluation is the original evaluation followed by $e$ and then this last value, giving the required decomposition.

**Key facts.** `BoolCircuit.StraightLine.runLines_snoc`.
