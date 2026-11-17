<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean :: Complexity.LogProg.move2_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Register Transfer Run

**Claim.** Under the stated control-flow, distinctness, and register-bound hypotheses, the transfer loop reaches its zero branch with $r$ set to zero and both $t$ and $t'$ increased by the original value of $r$, while preserving every other register and keeping every pre-final configuration within the bound and satisfying its applicable precondition.

**Proof.** Proceed by induction on the initial value $k$ of register $r$. If $k=0$, the zero test goes directly to $l_x$. The nested register updates in the stated endpoint reduce to the original valuation, since the three registers are distinct and $v(r)=0$. The initial configuration satisfies the guard, and reflexive reachability supplies the endpoint.

For the successor case, write $v(r)=k+1$. The zero test takes the nonzero branch to $l_1$. The decrement then changes $r$ to $k$, and the increment at $l_2$ increases $t$ by one; the increment at $l_3$ likewise increases $t'$ by one and returns to $l$. These intermediate configurations satisfy the guard: the preconditions at the four loop states follow from their instruction forms, and the register bounds follow from the given sums and the fact that each incremented register plus the remaining value of $r$ stays at most $B$. The induction hypothesis now applies to the returned configuration with $r=k$. It transfers the remaining $k$ units into each of $t,t'$, leaves all other registers unchanged, and reaches $l_x$. Combining the first iteration with that run gives the asserted total transfer; the distinctness assumptions ensure the updates have exactly the required endpoint values.

**Key facts.** `Complexity.LogProg.AReach.step`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.reach_of_eq`.
