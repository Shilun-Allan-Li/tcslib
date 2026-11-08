<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.registerCopy_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying one register by a loop

**Claim.** Under the stated instruction and value bounds, the comparison-and-increment loop reaches the done state with the destination equal to the source’s initial value, preserving the other registers, and the invariant and bound hold at every earlier configuration.

**Proof.** Let $k$ be the initial difference between the source and destination values. Induct on $k$. If $k=0$, the registers are equal, so the comparison immediately branches to $done$; the destination update is then the identity. The initial configuration satisfies the invariant because the comparison instruction has distinct registers, and all values are bounded by $B$. This one-step reach is supplied by the single-step reach fact (`AReach.single`).

For the successor case, the destination is strictly below the source. Increment it once, obtaining a value function $next$. Since the source is unchanged, the remaining difference is $k$; the induction hypothesis applies to $next$, and its values remain bounded by $B$ (`register_update_le`). The current comparison therefore branches to $bump$, and that instruction increments the destination and returns to $test$. The required invariant holds at these intermediate configurations: at the comparison state it follows from distinctness of the registers, and at the bump state the instruction is an increment. Prepending these two steps to the inductive reach gives the full reach, using the reach-step fact (`AReach.step`). The final destination value is the original source value, while every other register remains unchanged.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.step`.
