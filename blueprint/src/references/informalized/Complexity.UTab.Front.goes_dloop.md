<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.goes_dloop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Division-loop Register Update

**Claim.** If $1\le x_0$, then from the division-loop label with registers $(x_0,C+1,0,0,d)$, the program reaches its finishing label with registers $(x_0,(C+1)x_0^d,0,0,0)$, preserving input position and output, within $d\bigl(14(C+1)x_0^d+4\bigr)+1$ steps.

**Proof.** Put $T=(C+1)x_0^d$ and apply `goes_loop` to the fifth register, which counts down from $d$. After $j$ iterations the registers are $(x_0,(C+1)x_0^j,0,0,d-j)$. In each body, the main-loop transfer (`goes_aloop`) moves the current second-register amount into the third register while multiplying that amount by $x_0$; the branch loop (`goes_bloop`) then transfers the third register back into the second. Their runs compose by `Goes.trans`, and `upd_D` accounts for the outer counter decrement. The hypothesis $1\le x_0$ ensures $(C+1)x_0^j\le (C+1)x_0^{j+1}\le T$, which bounds the body cost by $14T+2$. The outer-loop principle therefore gives $d((14T+2)+2)+1=d(14T+4)+1$. `Goes.congr` and the register-tuple equalities yield the stated endpoint and bound.

**Key facts.** `Complexity.CounterProg.goes_loop`, `Complexity.UTab.Front.goes_aloop`, `Complexity.UTab.Front.goes_bloop`, `Complexity.CounterProg.Goes.trans`, `Complexity.UTab.Front.upd_D`, `Complexity.CounterProg.Goes.congr`, `Complexity.UTab.Front.rv_congr`.
