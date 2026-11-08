<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean :: Complexity.LogProg.move_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Transfer Loop

**Claim.** Under the stated control-flow and distinctness hypotheses, the loop reaches $l_x$ with $r$ zero and $t$ increased by the original value of $r$, leaving all other registers unchanged; every earlier configuration satisfies the program precondition and the bound $B$.

**Proof.** Induct on the initial value $k$ of $r$. When $k=0$, the zero test takes the branch to $l_x$. The endpoint's two nested updates then equal the original valuation, using $v(r)=0$ and $r\ne t$. The initial configuration satisfies the guard, and reflexive reachability finishes this case.

For $k+1$, the zero test takes the nonzero branch to $l_1$, the decrement changes $r$ to $k$, and the increment at $l_2$ raises $t$ by one and returns to $l$. Each of these configurations satisfies the guard: the corresponding instruction preconditions hold, and the register bounds follow from the original bounds and $v(t)+v(r)\le B$. Apply the induction hypothesis to this returned configuration, now with $r=k$ and $t$ already increased by one. It transfers the remaining $k$ units into $t$ and reaches $l_x$. Since $r$ and $t$ are distinct, the updates combine to set $r$ to zero and $t$ to its initial value plus $k+1$, while all other registers retain their values. The reachability step and endpoint-equality principle assemble the finite run and identify its endpoint with the claimed nested-update expression.

**Key facts.** `Complexity.LogProg.AReach.step`, `Complexity.LogProg.reach_of_eq`.
