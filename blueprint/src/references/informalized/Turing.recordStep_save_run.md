<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_save_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Counter-Saving Run

**Claim.** The counter-loop reaches escape with the input head at zero, true embedded state, and the counter decremented $p+1$ times within the stated time and head bounds; the complement of the resulting counter has value $p+1$.

**Proof.** The saving-machine orbit reaches true at input position zero after $p+1$ steps, while all earlier rounds remain false and each single-step body run has no intermediate state (`recordStep_save_orbit`). Since $p$ is below the initial counter value, the counter-loop escape theorem applies: it combines those body rounds with counter decrements, reaches escape, avoids both done and escape beforehand, and bounds the counter head in the interval from $cp-1$ to $cp+|w|$ (`counterLoopTM_run_escape`). Its endpoint identifies the embedded configuration with the stated true, zero-position configuration; equality of configurations with no work tapes follows from their state, input-position, and output fields (`Cfg.ext_zero_tapes`). The loop's overhead is at most $4(p+1)+2|w|$ (`counterOverhead_le_of_le`), so adding the $p+1$ body steps yields the given time bound. Finally, the counter value after $p+1$ decrements is its original value minus $p+1$ (`counterWord_value`), and the original all-ones word has value $2^{|w|}-1$. The complement-value identity therefore gives value $p+1$ for the complemented result (`recordStep_complement_value`).

**Key facts.** `Turing.recordStep_save_orbit`, `Turing.counterLoopTM_run_escape`, `Turing.Cfg.ext_zero_tapes`, `Turing.counterOverhead_le_of_le`, `Turing.counterWord_value`, `Turing.recordStep_complement_value`.
