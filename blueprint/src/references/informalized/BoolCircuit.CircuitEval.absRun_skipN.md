<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean :: BoolCircuit.CircuitEval.absRun_skipN -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skipping a unary natural code

**Claim.** Reading $n$ true bits followed by a false bit from the skip-count phase leaves the evaluator in its gate-parsing phase at the same position, with the same values and marked indices, ready to process the remainder.

**Proof.** Induct on $n$. When $n=0$, the first symbol is false, and the skip-count phase changes directly to gate parsing without changing the position or other data. For the successor case, the first true bit leaves the evaluator in the skip-count phase. The induction hypothesis then handles the remaining $n$ true bits, the terminating false bit, and the given remainder, yielding the stated gate-parsing run.
