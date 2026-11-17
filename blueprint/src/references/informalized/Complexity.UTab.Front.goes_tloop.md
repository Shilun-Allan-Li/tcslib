<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.goes_tloop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Temporary-register Loop

**Claim.** From the temporary-register test label with registers $(x_0,a,b,t,e)$, the program reaches the main-loop label with registers $(x_0+t,a,b,0,e)$, preserving input position and output, in at most $3t+1$ steps.

**Proof.** Apply `goes_loop` to the temporary register, which is tested at the loop head and decremented at the loop's decrement label. At iteration $j$, the registers are $(x_0+j,a,b,t-j,e)$. Each body iteration decrements the temporary register and then increments the first register before returning to the test; the increment step is justified by `goes_inc`, and `upd_Tm` and `upd_X` identify the register changes. Thus each body takes one step and appends nothing. The loop principle gives $t(1+2)+1=3t+1$ steps, including the final test. The final register assignment follows from the iteration formula, with `Goes.congr` aligning it with the stated tuple.

**Key facts.** `Complexity.CounterProg.goes_loop`, `Complexity.CounterProg.goes_inc`, `Complexity.UTab.Front.upd_Tm`, `Complexity.UTab.Front.upd_X`, `Complexity.CounterProg.Goes.congr`, `Complexity.UTab.Front.rv_X`, `Complexity.UTab.Front.rv_congr`.
