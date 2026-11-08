<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.goes_xloop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Counter Loop Iteration

**Claim.** Starting at label $\mathsf{xh}$ with registers $(x_0,a,b,t,e)$ and input position $p$, the program reaches $\mathsf{th}$ with registers $(0,a,b+x_0,t+x_0,e)$, unchanged input position, and no additional output, in at most $4x_0+1$ steps.

**Proof.** Apply the loop principle (`goes_loop`) with loop counter $r_X$, head $\mathsf{xh}$, decrement label $\mathsf{xd}$, body $\mathsf{x1}$, exit $\mathsf{th}$, and $K=x_0$. At iteration $j$, the register assignment is $(x_0-j,a,b+j,t+j,e)$ and the input position remains $p$. The head tests whether $r_X$ is zero; when it is positive, the decrement at $\mathsf{xd}$ is followed by increments of $r_B$ and $r_{Tm}$ at $\mathsf{x1}$ and $\mathsf{x2}$. Thus each body passage takes two steps after the decrement and returns to the head with the first register reduced by one and the third and fourth registers increased by one. The register lookup and update facts (`rv_B`, `upd_B`, `rv_Tm`, `upd_Tm`, `upd_X`) identify these changes, while register-assignment congruence (`rv_congr`) matches the resulting states. No instruction on this route reads input or appends output. After $x_0$ iterations, the head test exits at $\mathsf{th}$ with the stated registers. The loop bound is $x_0(2+2)+1=4x_0+1$ steps; the final register and bound equalities are the stated arithmetic bookkeeping.

**Key facts.** `Complexity.CounterProg.goes_loop`, `Complexity.CounterProg.goes_inc`, `Complexity.CounterProg.Goes.trans`, `Complexity.UTab.Front.rv_B`, `Complexity.UTab.Front.upd_B`, `Complexity.UTab.Front.rv_Tm`, `Complexity.UTab.Front.upd_Tm`, `Complexity.UTab.Front.upd_X`, `Complexity.UTab.Front.rv_congr`, `Complexity.CounterProg.Goes.congr`.
