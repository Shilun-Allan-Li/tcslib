<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.goes_bloop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Transfer Loop

**Claim.** Starting at the branch that tests the third register with registers $(x_0,a,b,0,e)$, the program reaches the branch that tests the fifth register with registers $(x_0,a+b,0,0,e)$, preserving input position and output, in at most $3b+1$ steps.

**Proof.** Use the counter-loop principle (`goes_loop`) with the third register as the loop counter. At iteration $j$, the register assignment is $(x_0,a+j,b-j,0,e)$. The loop body decrements the third register; the following instruction increments the second register and returns to the test. The one-step increment fact (`goes_inc`), together with `upd_B` and `upd_A`, verifies this state transition. Each body run takes one step and appends no output, so the loop principle gives a total bound of $b(1+2)+1=3b+1$. Finally, `Goes.congr` identifies the endpoint registers and bound with the claimed expressions.

**Key facts.** `Complexity.CounterProg.goes_loop`, `Complexity.CounterProg.goes_inc`, `Complexity.UTab.Front.upd_B`, `Complexity.UTab.Front.upd_A`, `Complexity.CounterProg.Goes.congr`, `Complexity.UTab.Front.rv_A`, `Complexity.UTab.Front.rv_congr`.
