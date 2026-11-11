<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.decD_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Decrementing Run Invariant

**Claim.** Starting with the register containing $\mathrm{pre}\mathbin{+}w$ and its head at the end of $\mathrm{pre}$, the decrement routine reaches its designated state with the register containing $\mathrm{pre}\mathbin{+}\mathrm{decW}(w)$ and the head in the stated range; all earlier configurations remain in the prescribed decrement phases and head interval.

**Proof.** Induct on the word $w$, retaining the arbitrary prefix $\mathrm{pre}$ throughout. If $w$ is empty, the head reads the blank immediately after the prefix. The decrement transition moves left into the designated state without changing the tape; the resulting head is at $|\mathrm{pre}|-1$. The only earlier time is the initial configuration, which has the required state and head position.

For a leading $0$, the decrement transition changes it to $1$ and advances one cell. The resulting configuration is exactly the starting configuration for the induction hypothesis on the remaining word, with extended prefix $\mathrm{pre}+[1]$. Concatenating this first step with the inductive run gives the target contents and state. The initial configuration satisfies the invariant directly, and each later pre-terminal configuration inherits the inductive state and head bounds after shifting positions by one.

For a leading $1$, the first transition changes it to $0$ and advances to the next cell. If there is no remaining bit, the left-scan phase sees blank and moves back to the changed bit; the clearing phase erases that final $0$ and moves left into the designated state. These three steps leave precisely the prefix and place the head at $|\mathrm{pre}|-1$. The only earlier configurations are the initial state, the left-scan state at the changed bit, and the clearing state at the prefix boundary; each has a head position between the prefix start and the original word end. If a further bit remains, the left-scan phase sees it and moves back into the designated state. The resulting register contains the prefix followed by $0$ and the untouched remainder, which is exactly the decrement result in this case; the two pre-terminal configurations have the required states and head bounds. In each case, canonicity supplies the induction hypothesis for the tail.

**Key facts.** `Complexity.LogProg.canon_tail`, `Complexity.LogProg.rrun_one_reg`, `Complexity.LogProg.regCfg_read`, `Complexity.LogProg.apply_regAct`, `Complexity.LogProg.update_bufferTape_cons`, `Complexity.LogProg.bufferTape_erase_last`, `Complexity.LogProg.rrun_add`.
