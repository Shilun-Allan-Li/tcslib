<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_inner_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner multiplication loop

**Claim.** Under the stated register bounds, endpoint and bit-reading assumptions, and index and sum bounds, the inner loop reaches the next outer-loop state, increasing registers $9$, $10$, and $11$ by $2|w|$, $|w|$, and the indicated contribution sum, respectively, while leaving the other registers unchanged and preserving the required conditions along the run.

**Proof.** Proceed by induction on the list $w$, generalizing the register assignment. If $w$ is empty, the endpoint relation says that registers $9$ and $5$ agree. The loop therefore exits directly to the next outer-loop state; the empty sum and empty-list length show that the registers are unchanged. The one-step reachability principle verifies the invariant at the starting configuration.

For $w=u::w'$, set $\delta=[v(10)=v(7)]\,b\,u$, where bits are regarded as natural numbers. The contribution lemma shows that the program processes the first pair of bits and adds $\delta$ to register $11$. It then advances register $9$ twice and register $10$ once, arriving at the inner-loop state with these updated registers. The register-update bound lemma, together with the assumed index and sum bounds, verifies the register bound at each intermediate assignment. The input-reading assumptions give the required first-bit fact and transfer the remaining reading facts to the shifted indices. The decomposition of the contribution sum for a cons list (the lemma `Complexity.multRow_cons`) gives the sum bound needed for the induction hypothesis on $w'$. Applying that hypothesis completes the run; arithmetic on the accumulated updates identifies the final registers with the claimed values. Reachability composition combines the contribution step, the three advances, and the inductive run, and one initial step accounts for the loop's entry instruction.

**Key facts.** `Complexity.LogProg.AReach.single`, `Complexity.LogProg.register_update_le`, `Complexity.multRow_cons`, `Complexity.mult_contribution`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.step`.
