<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_clean_buffer_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the retained word

**Claim.** For each $j\le |y|$, the clean wrapper starting in control state 4 at capture-head position $j-1$ reaches control state 5 at position zero after exactly $j+1$ steps, preserving the retained word and input position.

**Proof.** Proceed by induction on $j$. When $j=0$, the capture head is at position $-1$, so the buffer is blank there. The first transition from state 4 moves the capture head right to zero and enters state 5; the zero-time run identity and the buffer-action calculation give the claimed endpoint in one step. For the successor case, the starting position is $j$. Since $j<|y|$ by the induction hypothesis on the bound, the scanned symbol is the $j$th bit of $y$, so state 4 moves left and remains in state 4. The buffer-action formula identifies this configuration with the induction hypothesis's starting configuration, whose capture-head position is $(j: \mathbb Z)-1$. Applying the induction hypothesis completes the run in $j+1$ further steps; together with the initial step this is $(j+1)+1$ steps. The retained buffer and input-head position are unchanged throughout.

**Key facts.** `Complexity.enumCont_buffer_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
