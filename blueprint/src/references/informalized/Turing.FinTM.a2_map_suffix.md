<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_suffix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying an input suffix

**Claim.** Starting in the copying phase with the stated head positions and buffers, after $|r|+1$ steps the simulator is in the return-to-buffer phase with $r$ appended to the second buffer and the specified final head positions.

**Proof.** Induct on the suffix $r$, maintaining the prefix and buffer data in the statement. If $r$ is empty, the input head is at the end marker, so one copying-phase transition switches to the return-to-buffer phase. The first buffer and its head are unchanged; the second head moves left once, giving the stated position for the unchanged second buffer. If $r=d::r'$, the next input symbol is $d$. The copying transition writes $d$ into the second buffer, advances the input head, and advances that buffer’s head, leaving the first buffer and output unchanged. The buffer extension identity `bufferTape_append` verifies that this write produces the tape representation of $b++[d]$; the tape-block indexing fact `tapeBlocks_buffer` identifies the simulator’s second tape. The head movement is the stated rightward input move (`moveInputPos_pos_of_ne_right`), and the transition’s effect on heads and output is recorded by `a2_map_move`. Apply the induction hypothesis to the remaining suffix $r'$ with prefix extended by $d$ and buffer extended by $d$. Its run length is $|r'|+1$, so including the first copying step gives $|r|+1$ steps and the desired final configuration. The run-length decomposition uses `runFrom_succ_eq_step` in the inductive step, and `runFrom_zero` in the empty case.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.a2_mapCfg_read`, `Turing.FinTM.a2_map_move`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.bufferTape_append`, `Turing.FinTM.tapeBlocks_buffer`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
