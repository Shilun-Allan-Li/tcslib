<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Scan.lean :: Turing.writeConstTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writing and Returning to the Origin

**Claim.** Starting in the initial writing phase, the machine writes $w_0$ on tape $i$, returns that tape's head to its initial position, and reaches the done state after $2|w_0|+2$ steps. Before then it is not done, and its heads obey the stated bounds.

**Proof.** The run is represented at every time by a three-part trace: a forward writing scan, a return scan, and the done phase (`scan_const_trace`). At time $2|w_0|+2$, the trace is in its done phase; expanding that phase and the writing configuration gives the asserted tape contents, with all cells outside the written interval unchanged. For any earlier time, the trace is in the writing or return phase, so the state is not done. For the head bounds, consider times before completion along the trace: the writing scan moves from the initial position toward the end of the word, and the return scan moves back along that same interval; other heads are stationary. At completion the head has returned to its origin. The interval from the initial position through the position $|w_0|$ cells to its right therefore contains the selected head throughout.

**Key facts.** `Turing.scan_const_trace`.
