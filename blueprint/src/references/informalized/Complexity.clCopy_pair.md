<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCopy_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-step Copying of One Bit

**Claim.** Starting in the copier's reading control with source word $u b v$, source head at $|u|$, and record $r$, two steps preserve the source and input-head position, advance the source head by one, append $bb$ to the record, and remain in the reading control.

**Proof.** At source position $|u|$, the source tape contains $b$ (`Turing.FinTM.bufferTape_nat` identifies the tape symbol there with the corresponding list entry). The first transition writes $b$ to the record and moves the record head forward, entering the intermediate control (`clCopy_write`). The next transition reads the same source bit, writes a second $b$, advances the source head by one, and returns to the reading control (`clCopy_write`). Combining these transitions with the zero-step and successor descriptions of an iterated run gives the stated two-step configuration.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Complexity.clCopy_write`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`.
