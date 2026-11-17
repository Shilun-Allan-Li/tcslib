<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.goes_rT -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Step-Count Scan

**Claim.** If the input is a prefix, followed by $b$ true bits and a remainder, then starting at $rT$ after the prefix reaches $rT$ after scanning those bits. The step-count register increases by $b$, the input position advances by $b$, the other registers and output are unchanged, and the run takes at most $2b$ steps.

**Proof.** Proceed by induction on $b$, generalizing the prefix. If $b=0$, the input decomposition gives the desired unchanged configuration, and reflexivity of the run relation supplies a run of zero steps. For the successor case, the input decomposition shows that the next symbol at the current position is true. Reading it at $rT$ consumes one input symbol and moves to $tInc$ (the true-input read rule, `goes_rd_true`); incrementing the step-count register then returns to $rT$ (the register-increment rule, `goes_incR`). Apply the induction hypothesis to the remaining $b$ true bits, using the extended prefix and the record whose step-count register has already increased by one. The run-composition rule (`Goes.trans`) concatenates these three runs, preserving their register and position updates and adding their step bounds. Finally, the register and position arithmetic identifies the resulting record and position with the claimed ones, and the bound is $1+1+2b=2(b+1)$. The comparison rule (`Goes.congr`) aligns the resulting register function, position, empty extra output, and step bound with the statement.

**Key facts.** `Complexity.CounterProg.goes_refl`, `Complexity.CounterProg.goes_rd_true`, `Complexity.UTab.goes_incR`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.Goes.congr`.
