<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Setup.lean :: Complexity.LogProg.SavitchARM.pw_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Loop Execution

**Claim.** For every exponent-counter value $j$, if the stated register, scratch, positivity, and product bounds hold, the power loop reaches the radius-copy routine with counter zero and accumulator $P a^j$, without recording an answer, while respecting the guard throughout.

**Proof.** Proceed by induction on $j$. When $j=0$, the loop tests the zero exponent counter and immediately enters the radius-copy routine; the accumulator is already $P=P a^0$. The one-step execution preserves the guard, and reflexive reachability accounts for the remaining run to the stated endpoint. For the successor case, first test the counter and decrement it, changing $X=j+1$ to $j$. The accumulator bound needed for the ensuing multiplication follows from $P\le P a^{j+1}\le B$ and $Pa\le P a^{j+1}\le B$, using $a\ge1$. The multiplication routine with multiplier $a$ therefore changes $P$ to $Pa$ and returns to the power-loop test with the other required register conditions intact. Apply the induction hypothesis at counter $j$ and accumulator $Pa$: its product bound is $(Pa)a^j=P a^{j+1}\le B$. The induction run ends with accumulator $(Pa)a^j=P a^{j+1}$ and counter zero. Concatenating the initial test and decrement, multiplication run, and induction run proves the result; the step and multiplication reachability facts ensure the guard throughout.

**Key facts.** `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.SavitchARM.step_of`, `Complexity.LogProg.SavitchARM.mul_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.reach_of_eq`.
