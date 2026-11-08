<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.counter_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count and Carry Successors Agree

**Claim.** For a binary input word $x$, a position $i<|x|$, and any tape contents $b$, the one-step successor from the count state at input position $i+1$ equals the one-step successor from the carry state at position $i+2$, when both configurations have work-head position $0$ and empty output.

**Proof.** The input symbol at position $i+1$ is $x_i$: this is the input-symbol evaluation fact `inputSymbolInner`. Thus both transitions see the same input bit. By the definition of the length-bits machine, the count-state transition on that bit agrees with the carry-state transition on the same bit; after unfolding the counter update, the only remaining cases are whether the tape at coordinate $0$ contains `true`. In either case the successor states, tape contents, work-head positions, and outputs agree. For the input head, the first configuration moves right from $i+1$, while the second stays at $i+2$. Since $i<|x|$, the first position is not the right boundary, so the right-move formula gives position $i+2$ (`moveInputPos_pos_of_ne_right`); staying put preserves the second position (`moveInputPos_zero`). Hence all configuration fields agree.

**Key facts.** `Turing.inputSymbolInner`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.moveInputPos_zero`.
