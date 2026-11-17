<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean :: Complexity.LogProg.dmove_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Register Transfer

**Claim.** Under the stated instruction pattern and register bounds, a finite run transfers twice the initial value of $r$ into $t$, resets $r$ to zero, and satisfies the guard at every configuration before the endpoint.

**Proof.** Proceed by induction on the initial value $k=v(r)$. If $k=0$, the zero test branches directly to $l_x$. No register changes, and the target valuation agrees with the starting valuation because the two updates set $r$ to zero and add $2v(r)=0$ to $t$. The starting configuration satisfies the guard, so reflexivity gives the required guarded reachability.

For the successor case, write $v(r)=k+1$. The zero test takes its nonzero branch to $l_1$, and the decrement leads to $l_2$, reducing $r$ to $k$. The first increment of $t$ then leads to $l_3$, and the second increment returns to $l$. These four configurations satisfy the guard: the unchanged valuation is bounded by hypothesis, and each updated valuation remains bounded by the relevant upper bound, using $v(t)+2v(r)\le B$ and the fact that $r\ne t$. The induction hypothesis now applies to this returned configuration, whose $r$-value is $k$; it reaches $l_x$ with $r=0$ and adds $2k$ to $t$. Concatenating the four steps with that inductive run gives the desired endpoint, since the two increments contribute $2$ and the recursive transfer contributes $2k$. The reachability composition facts `AReach.step` and `reach_of_eq` assemble the guarded steps and identify the resulting valuation; `register_update_le` supplies the bounds after each register update.

**Key facts.** `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.AReach.step`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.reach_of_eq`.
