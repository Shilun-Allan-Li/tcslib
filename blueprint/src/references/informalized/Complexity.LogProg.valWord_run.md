<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.valWord_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean-word scan simulation

**Claim.** Under the value-word and rewind transition assumptions, the scan reaches the next state at input position $1$ exactly when the last bit of the word, or the remembered bit for an empty word, is not false. If that bit is false, it rejects. The run preserves the specified register-head positions and avoids call states before its endpoint.

**Proof.** First observe that the three scanning states selected by the remembered bit have exactly the stated value-word transitions and are all non-call states. Induct on the length of $w$, keeping the alignment equation $q+|w|=|x|+1$. For a nonempty word $w=b::u$, the first transition reads $b$ and moves right into the state remembering $b$, by `reaches_right`. The remaining suffix is aligned starting at $q+1$, so the induction hypothesis applies to $u$ with remembered bit $b$. The last-bit condition for $b::u$ equals the corresponding condition for $u$ with that remembered bit: if $u$ is empty it is $b$, and otherwise it is the last bit of $u` (`getLast?_cons_of`). Prefix the inductive reach or rejection with the first step using `Reaches.step` or `Rejects.step`.

For the empty word, alignment places the head at the right boundary. If the remembered bit is not false, the state takes the transition into $r_1$; `rewind_x` then shows that the rewind states return the head to position $1$ and reach `next`, with all intermediate states non-call. If the remembered bit is false, the boundary transition rejects directly (`rejects_one`). At every stage, the transition identities ensure no movement of the register head. The transition calculations use `apply_xAct` and `rrun_one_x`; `none_orElse'` simplifies the empty-word last-bit condition. Thus induction proves both alternatives and their intermediate-state invariants.

**Key facts.** `Complexity.LogProg.getLast?_cons_of`, `Complexity.LogProg.none_orElse'`, `Complexity.LogProg.reaches_right`, `Complexity.LogProg.rewind_x`, `Complexity.LogProg.Reaches.step`, `Complexity.LogProg.Rejects.step`, `Complexity.LogProg.rejects_one`, `Complexity.LogProg.apply_xAct`, `Complexity.LogProg.rrun_one_x`.
