<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.goes_aloop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Main-loop Register Transfer

**Claim.** Starting at the main-loop label with registers $(x_0,a,b,0,e)$, the program reaches the return-to-transfer label with registers $(x_0,0,b+a x_0,0,e)$, without changing the input position or output, in at most $a(7x_0+4)+1$ steps.

**Proof.** Apply the general counter-loop principle to the main loop, whose tested register is the second register and whose body first decrements it. At iteration $j$, the registers are $(x_0,a-j,b+jx_0,0,e)$. After the decrement, the inner $x$-loop transfers $x_0$ units from the first register to the third, and the temporary-register loop restores the first register; together these return to the main-loop test with the second register decreased by one and the third increased by $x_0$. The inner-loop facts are `goes_xloop` and `goes_tloop`; their runs compose with `Goes.trans`. The register updates are identified using `upd_A` and equality of register assignments (`rv_congr`). Thus each body iteration takes at most $7x_0+4$ steps and prints nothing. The outer-loop principle (`goes_loop`) runs this body $a$ times and adds the final test step, giving $a(7x_0+4)+1$. The endpoint register assignments and bound are then matched to the stated forms using `Goes.congr` and elementary arithmetic.

**Key facts.** `Complexity.CounterProg.goes_loop`, `Complexity.UTab.Front.goes_xloop`, `Complexity.UTab.Front.goes_tloop`, `Complexity.UTab.Front.upd_A`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.Goes.congr`, `Complexity.UTab.Front.rv_congr`.
