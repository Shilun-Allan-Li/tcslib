<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEval.lean :: BoolCircuit.CircuitEval.decidesInTime_of_verdict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic-time decision from a verdict

**Claim.** If membership in a Boolean-word language $L$ is equivalent to the machine verdict being true, then the evaluator decides $L$ in time $12(n+1)^2$.

**Proof.** Fix an input $z$. The assumed characterization identifies the language indicator of $z$ with the Boolean verdict: if $z\in L$, both are true; if $z\notin L$, the verdict cannot be true, so both are false. The evaluator computation theorem supplies a halting run of the stated length that outputs the one-bit verdict (`evalTM_computes`). Replacing that verdict with the equal indicator gives exactly the output required in the definition of deciding $L$ within the quadratic bound.

**Key facts.** `BoolCircuit.CircuitEval.evalTM_computes`.
