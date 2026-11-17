<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_copy_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Certificate Copy Run

**Claim.** When the input is a prefix followed by a binary word $u$, after any $j\le |u|$ steps in the copy state the verifier has consumed the prefix and the first $j$ bits of $u$, stores that length-$j$ prefix on its work tape, and has its work head at position $j$.

**Proof.** Induct on $j$. At $j=0$, the machine is in the stated starting configuration, and the empty prefix of $u$ is stored. For the induction step, let $j<|u|$. The input-reading fact for these configurations (`Complexity.taut_read`) identifies the next input symbol with the $(j+1)$st bit of $u$. The machine's copy transition advances the input head, writes that bit at the current work-head position, advances the work head, and remains in the copy state. The run-successor identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) turns the induction hypothesis followed by this transition into the run of length $j+1$. The input-head movement formula (`Turing.moveInputPos_pos_of_ne_right`) gives the new consumed-input count; the bound $j<|u|$ ensures this move is before the right boundary. The updated tape contains exactly the first $j+1$ bits: appending the new bit updates the buffer tape at its previous end (`Turing.FinTM.bufferTape_append`). The state and empty output are preserved, and the work head is now at $j+1$, completing the induction.

**Key facts.** `Complexity.taut_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`.
