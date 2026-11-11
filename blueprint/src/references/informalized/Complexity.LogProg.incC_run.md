<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean :: Complexity.LogProg.incC_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the increment carry-in phase

**Claim.** The carry-in phase reaches state $c_B$ with tape $\mathrm{pre}\mathbin{++}\mathrm{incW}(w)$ at some head position in the stated range, and every earlier configuration remains in state $c_C$ with the stated head-position bounds.

**Proof.** Induct on the word $w$. If $w$ is empty, the head is at the end of the prefix and reads no symbol. The carry-in transition writes a one there, moves left, and enters $c_B$. The buffer-tape update-at-end identity (`update_bufferTape_end`) identifies the resulting tape with $\mathrm{pre}\mathbin{++}[1]$, which is the incremented empty word appended to the prefix. The only earlier configuration is the starting one and satisfies the bounds. If $w$ begins with zero, the head reads that zero; the carry-in transition changes it to one, moves left, and enters $c_B$. The update-at-a-list-position identity (`update_bufferTape_cons`) identifies the tape with the prefix followed by the incremented word. Again the sole earlier configuration is the start. If $w$ begins with one, the transition changes that bit to zero and moves right, leaving the state at $c_C$. The remaining computation is the induction hypothesis on the tail, with the prefix extended by a zero. Compose the first step with that run using the iteration addition law (`rrun_add`). For earlier times, separate the initial time from times after the first step; the induction bounds on the latter, adjusted for the extended prefix, give the required head-position bounds and preserve state $c_C$.

**Key facts.** `Complexity.LogProg.rrun_one`, `Complexity.LogProg.rstep_noncall`, `Complexity.LogProg.regCfg_state`, `Complexity.LogProg.regCfg_read`, `Complexity.LogProg.apply_regAct`, `Complexity.LogProg.update_bufferTape_end`, `Complexity.LogProg.update_bufferTape_cons`, `Complexity.LogProg.rrun_add`.
