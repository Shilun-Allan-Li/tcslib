<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean :: Complexity.LogProg.shl_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Doubling by a Logarithmic Loop

**Claim.** Under the stated transition pattern and register bounds, the program reaches the configuration that sets $c$ to zero and replaces $r$ by its initial value times $2^{v(c)}$, leaving all other registers unchanged; every earlier configuration satisfies the guard.

**Proof.** Use induction on the initial value $k$ of register $c$.

1. If $k=0$, the first zero test branches directly to $l_x$. The target register update is the identity: $c$ was already zero, and the requested value of $r$ is $v(r)2^0=v(r)$. The initial configuration satisfies the guard by the assumed register bounds and the fact that the zero test has no additional safety condition. Reachability follows by one guarded step and reflexivity at the endpoint (`AReach.step`, `AReach.refl`).

2. Suppose $k>0$. The assumed bound $v(r)2^k\le B$ implies $2v(r)\le B$, since $2^k\ge2$. The first test and decrement reduce $c$ from $k$ to $k-1$, preserving the bound on every register; the updated value of $c$ is at most $B$ as well. Now the loop at $l_2$ processes the current value $v(r)$ with the scratch register $z$ initially zero. The two-to-one transfer result (`dmove_run`) carries out the decrement-and-double cycle: it clears the current counter and adds twice its value to $z$, while preserving the register bound. The control then uses the zero test and return loop at $l_6$ to move the accumulated amount from $z$ back into $r$ (`move_run`). The pairwise distinctness assumptions ensure that these updates leave the other relevant registers intact. Chaining these reachability segments (`AReach.trans`) yields the state at the start of the next outer iteration: $c=k-1$, $z=0$, and $r$ equal to twice its value before this iteration.

3. The intermediate register values remain bounded: each transfer theorem supplies guarded reachability, and the register-update bound (`register_update_le`) preserves the global bound whenever an updated value is at most $B$. The arithmetic hypothesis also supplies the induction bound for the new value of $c$: rewriting $2^k=2^{k-1}\cdot2$ gives $(2v(r))2^{k-1}=v(r)2^k\le B$. Apply the induction hypothesis to this next-iteration configuration. After that recursive run, $r$ is $2v(r)2^{k-1}=v(r)2^k$, while $c$ and $z$ are zero. Register extensionality and the pairwise distinctness of $c,r,z$ identify this configuration with the claimed target. Reachability to that target follows by concatenation and endpoint equality (`reach_of_eq`).

**Key facts.** `Complexity.LogProg.AReach.step`, `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.dmove_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.move_run`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.reach_of_eq`.
