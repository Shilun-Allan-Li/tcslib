<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.extract_suffix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extractor Suffix Copying

**Claim.** With the second flag true, starting in suffix state at the beginning of $r$ halts after $|r|+1$ steps, advances the input head to the end of $x$, leaves the buffer and work head unchanged, and appends $r$ to the output.

**Proof.** Induct on the suffix $r$. If it is empty, the next transition reads the end marker and halts without emitting a bit. The one-step run equation together with the zero-step run equation (`runFrom_succ_eq_step`, `runFrom_zero`) gives the claimed final configuration. If $r=b::s$, the current transition reads $b$ by the input-position reading fact (`extractCfg_read`). Since the second flag is true, suffix state copies that bit to the output and moves the input head one place right, leaving the buffer and work head unchanged. The positive input-head movement fact (`moveInputPos_pos_of_ne_right`) verifies this position update. The induction hypothesis then processes $s$ from the advanced input position and output extended by $b$. Combining the first step with that run using `runFrom_succ_eq_step` yields halted state, end-of-input position, unchanged work data, and output $o++b::s=o++r$.

**Key facts.** `Turing.FinTM.extractCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
