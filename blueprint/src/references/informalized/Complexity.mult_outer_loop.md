<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_outer_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer multiplication loop

**Claim.** Under the stated reading, endpoint, index, and sum hypotheses, the outer loop reaches the result-test state with registers $0$, $8$, and $11$ increased by the claimed amounts, the other specified registers unchanged, and all register bounds and instruction side conditions preserved.

**Proof.** Induct on $a$, generalizing the register assignment. If $a$ is empty, the endpoint equation gives $v(0)=v(4)$, so the loop exits directly to the result-test state. Choose the final assignment to be $v$ itself; the empty sum and length establish the claimed register equations, and the other-register condition is immediate.

For $a=t::a'$, initialize the inner-loop registers by setting $9$ to $v(2)$ and $10$ to $v(8)$. The row-start lemma reaches the inner-loop state with this initialization. Apply the inner-loop lemma to the bit $t$ and list $b$: it advances registers $9$ and $10$ by $2|b|$ and $|b|$, and adds the row contribution to register $11$. The register-update bound lemma and the assumed index and sum bounds establish the required bounds for these intermediate assignments. The decomposition identity for `multRows` (`Complexity.multRows_cons`) shows that the row contribution plus the remaining rows is the full sum, with the latter evaluated at the shifted column offset. The program then advances the input position by two and the outer index by one, restoring the outer-loop state. The hypotheses for the induction on $a'$ follow by shifting the bit-reading indices and using the updated endpoint, index, and sum equations. The induction hypothesis supplies the remaining run and final assignment. Its register equations and frame property combine with the one-step updates to give the required final values and unchanged registers. Finally, compose the initial outer-loop step, row-start run, inner-loop run, advances, and inductive run.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.multRows_cons`, `Complexity.mult_row_start`, `Complexity.mult_inner_loop`, `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.step`, `Complexity.mult_preconditions`.
