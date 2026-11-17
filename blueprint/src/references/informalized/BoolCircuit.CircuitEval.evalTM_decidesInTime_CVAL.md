<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEval.lean :: BoolCircuit.CircuitEval.evalTM_decidesInTime_CVAL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit-value decision by the evaluator

**Claim.** In exact mode, the evaluator decides the language of encodings of fan-in-two Boolean circuits and inputs on which they evaluate to true, halting within the stated quadratic time and outputting the membership indicator.

**Proof.** The general verdict-to-decision theorem says that any language whose membership is equivalent to a true machine verdict is decided by the evaluator within the quadratic bound (`decidesInTime_of_verdict`). For the circuit-value language, the membership characterization identifies membership exactly with the verdict being true (`mem_CVAL_iff`). Apply the general theorem with the exactness flag set to true and this characterization as its hypothesis.

**Key facts.** `BoolCircuit.CircuitEval.decidesInTime_of_verdict`, `BoolCircuit.mem_CVAL_iff`.
