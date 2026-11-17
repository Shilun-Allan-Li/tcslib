<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Scan.lean :: Turing.inputCopyTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the Input-Copy Machine

**Claim.** Starting in the forward-scan state with input head at position $1$, the input-copy machine finishes after $2|x|+2$ steps with the stated copy on tape $i$, is never done earlier, and keeps the selected tape head within the stated interval while all other work-tape heads remain fixed.

**Proof.** Use the trace description of the run, which identifies the configuration at each time with the corresponding catalogued scan-copy trace (`Turing.scan_copy_trace`). At time $2|x|+2$, this trace is the designated done configuration. Its selected tape has the buffered word on precisely the interval from its initial head position through the next $|x|-1$ cells; outside that interval and on other tapes, it agrees with the original contents. At every earlier time, the trace is in one of the forward-scan or rewind portions, not the done state. Finally, inspecting the trace’s head positions across those portions shows that tape $i$ moves no farther left than one cell before its starting point and no farther right than $|x|$ cells after it; the other tape heads are unchanged. The endpoint bounds follow from the same trace description.

**Key facts.** `Turing.scan_copy_trace`.
