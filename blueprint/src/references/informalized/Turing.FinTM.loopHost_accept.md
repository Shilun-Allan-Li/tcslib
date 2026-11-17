<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_accept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output of a Halted Body Call

**Claim.** For a halted body configuration with output $o$, the loop host started from the specified call halts within $2|o|+3$ steps and outputs $o$ in find mode, or the one-bit word $[\mathrm{true}]$ otherwise.

**Proof.** Write the starting call as a controller frame using the call-to-frame description (`loopCall_frame`): it has phase seven, the flag set at zero, the given word on its track, and $o$ on the payload track. The frame's flag-read fact (`loopFrame_flag`) shows that the host sees the true flag. Its next transition therefore branches on find mode. In non-find mode, one step emits true and halts, giving the claimed output and a time within the bound. In find mode, the host moves to payload-scanning phase twelve. After the transition, the run-length identities `runFrom_succ_eq_step'` and `runFrom_add` split off that first step and organize the remaining scan. The payload-scan fact (`loopHost_payload_scan`) carries out the scan to phase thirteen; the frame-replay fact (`loopHost_frame_replay`) then says that after $|o|+1$ further steps the host halts with output $o$. Together with the initial transition this is $2|o|+3$ steps, as required.

**Key facts.** `Turing.FinTM.loopCall_frame`, `Turing.FinTM.loopFrame_flag`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.loopHost_payload_scan`, `Turing.FinTM.loopHost_frame_replay`.
