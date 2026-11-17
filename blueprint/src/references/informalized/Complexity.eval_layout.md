<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.eval_layout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation at layout zero

**Claim.** For a valid source with layout index zero, evaluating it on any block list gives the same value as evaluating it on the empty block list.

**Proof.** Split according to the form of the bit source. If it is an input bit, its value is read from the input list and does not depend on the block list. If it is a constant, its value is the same constant in either evaluation. In the remaining case the source is a block bit with instruction index $a$; validity at layout index $0$ would require $a<0$, which is impossible. Thus only the first two cases can occur, and their evaluations agree.
