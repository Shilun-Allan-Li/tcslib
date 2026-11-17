<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMLoops.lean :: Complexity.LogProg.sub_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Subroutine Run

**Claim.** Starting with register $q$ equal to $k$ at state $l$, the program can reach $l_x$ with $q$ set to zero, $r$ decreased by $k$ with truncated subtraction, all other registers unchanged, and no result set, while satisfying the guard and register bound at every earlier step.

**Proof.** Proceed by induction on $k$. If $k=0$, the zero-test at $l$ takes the branch directly to $l_x$. The target valuation is the original valuation: updating $q$ to zero changes nothing, and subtracting $v(q)=0$ from $r$ also changes nothing. The starting configuration satisfies the guard, and the reachability reflexivity fact (`AReach.refl`) supplies the remaining zero-length run.

For the induction step, suppose $v(q)=k+1$. The zero-test takes the nonzero branch to $l_1$. The decrement at $l_1$ takes the program to $l_2$ and changes $q$ from $k+1$ to $k$. The register bound still holds: this decrement does not increase any register, and the updated valuation satisfies the required side conditions. The decrement at $l_2$ then reduces $r$ by one and returns to $l$. Since $q\ne r$, it leaves $q=k$ unchanged; the register bound is preserved because $r$ has only decreased. At this point apply the induction hypothesis to the returned configuration, with $q=k$ and the updated valuation. It reaches $l_x$, reducing $r$ by a further $k$ and setting $q$ to zero. Combining the three initial transitions with that inductive run gives the required guarded run. The final updates agree with the stated target: $q$ is zero and $r$ has undergone $k+1$ truncated decrements, equivalently $v(r)-v(q)$ with natural-number truncated subtraction; all other registers and the unset result are preserved.

**Key facts.** `Complexity.LogProg.AReach.step`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.reach_of_eq`.
