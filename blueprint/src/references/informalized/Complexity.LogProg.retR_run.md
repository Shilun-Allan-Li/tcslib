<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean :: Complexity.LogProg.retR_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoring a Register Head

**Claim.** Under the stated endpoint, buffer, and side conditions, the register-return procedure reaches its successor after finitely many steps, placing the selected register head at zero and leaving the other register heads and all decider-head positions unchanged. Throughout, each register head obeys the stated bounds.

**Proof.** Read the selected register at its current head position using the buffer-tape convention. If its position is $-1$, that read is blank. The left-side hypothesis makes the non-scanning return transition move right immediately; one step therefore reaches the successor, updates this head to zero, and leaves all other head positions fixed. The asserted bounds hold at the initial and final configurations. This is the first branch of the proof.

Otherwise, the head position is a nonnegative integer $n$. If the current read is blank, the word-end hypothesis forces the target to be on the right; if it is not blank, the head is within the word. In either case the first transition moves the selected head one position left and enters the scanning phase. The scan lemma (`Complexity.LogProg.retR_scan`) applies from there: it scans left to the blank preceding the word, then moves right to position zero and advances to the successor. Its endpoint also leaves all other register heads and the decider-head positions fixed, and supplies the required bounds throughout the scan.

Composing the initial left move with this scan yields the claimed finite run. The one-step configuration calculation uses the register-move update rule (`Complexity.LogProg.apply_regMove`); run composition uses `Turing.MultiTapeTM.runFrom_succ_eq_step`.

**Key facts.** `Complexity.LogProg.apply_regMove`, `Complexity.LogProg.mkCfg_state`, `Complexity.LogProg.retR_scan`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
