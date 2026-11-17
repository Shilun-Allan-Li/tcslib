<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satPair_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the captured word

**Claim.** For $n\le |u|$, the pairing machine starting in state 3 with its capture head at offset $n-1$ reaches state 4 with that head at offset zero after exactly $n+1$ steps, leaving the other configuration data unchanged.

**Proof.** Induct on $n$. When $n=0$, the head is at offset $-1$, where the buffer tape has no symbol (Turing.FinTM.bufferTape_left). State 3 therefore takes its empty-buffer transition, moving the capture head one step right to offset zero and entering state 4. The canonical action lemma (Complexity.satPairAction_apply) verifies this update; the run-zero and run-successor laws (Turing.MultiTapeTM.runFrom_zero and Turing.MultiTapeTM.runFrom_succ_eq_step) express it as one step. For the successor case $n+1$, the buffer head at offset $n$ reads the $n$th symbol of $u$, since $n<|u|$. State 3 moves the capture head one position left and remains in state 3. The buffer lookup and canonical action lemma (Complexity.satPairCfg_work and Complexity.satPairAction_apply) show that the new offset is $n-1$, with all other fields preserved. The induction hypothesis then rewinds the remaining $n$ positions in $n+1$ steps. Together with this first step the total is $n+2$, as required for the successor case.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.satPairCfg_work`, `Turing.FinTM.bufferTape_left`, `Complexity.satPairAction_apply`.
