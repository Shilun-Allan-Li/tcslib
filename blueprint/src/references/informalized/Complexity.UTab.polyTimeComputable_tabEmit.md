<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.polyTimeComputable_tabEmit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Tableau Emission

**Claim.** For every finite Boolean Turing machine $M$, the tableau emitter is polynomial-time computable with the stated cubic time bound.

**Proof.** Fix an input $w$. The execution analysis theorem supplies register values and an execution of the program that reaches its halting state after some number $B$ of steps, with the correct output; it also bounds $B$ by $\operatorname{emitC}(M)(|w|+1)^3$ (goes_any). Apply the exact-run theorem to this execution and this upper bound: the program run for the full stated budget has the same halted configuration and output (run_budget). Thus, for every input, there is a halting run within the cubic bound whose output is the tableau emitter's value. The counter-program polynomial-time theorem turns this uniform bounded-time computation into polynomial-time computability, with exponent $3$ and coefficient $\operatorname{emitC}(M)$ (CounterProg.polyTimeComputable).

**Key facts.** `Complexity.UTab.goes_any`, `Complexity.UTab.run_budget`, `Complexity.CounterProg.polyTimeComputable`.
