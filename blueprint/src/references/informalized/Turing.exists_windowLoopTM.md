<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.exists_windowLoopTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulating a bounded window run

**Claim.** There is a finite-state machine that, from a record of a configuration and tag, simulates any prescribed number of steps of the window-limited run, records the resulting configuration and tag, and distinguishes halt, window exit, and clock exhaustion. It has the stated time and head-displacement bounds, preserves output, and does not enter a stop state early.

**Proof.** First obtain machines that test records and perform one simulated step on a record. Combine them into a loop machine whose control alternates between testing whether the represented configuration has halted and carrying out one window-respecting step. For each number $N$ of simulated steps, prove the loop guarantee by induction on $N$. At $N=0$, the run is exhausted immediately, so the record is unchanged and the loop takes zero steps. At the successor stage, one loop round either detects an already halted configuration, detects that its next step leaves the window, or patches the record to the next configuration and updated tag. In the latter case, apply the induction hypothesis to the patched record and concatenate the two machine segments. The record-patching lemmas preserve the record format and ensure that the final patch is exactly the record of the resulting window run. The per-round cost and the inductive bound give the claimed total time; the segment bounds control head displacement, while the loop construction preserves output and keeps its stop states fixed once reached.

Finally, use this loop guarantee for every finite horizon to obtain uniform bounds for all times, and use the machine's output-prefix property to conclude output is unchanged at intermediate times as well as at the endpoint. If the window run is exhausted, the chosen endpoint cannot occur before the horizon; if it halts or leaves the window, the corresponding distinct stop control is reached and was not reached earlier. The finite-step head bound yields the stated visited-space bound. The finite-set sum and record-length identity supply the bookkeeping needed to express these bounds using the stated record length.

**Key facts.** `Turing.exists_recordTestTM`, `Turing.exists_recordStepTM`, `Turing.wl_round`, `Turing.Segment.zero`, `Turing.Segment.trans`, `Turing.wl_patch_record`, `Turing.wl_patch_patch`, `Turing.wl_patch_self`, `Turing.MultiTapeTM.runFrom_add`, `Turing.wl_stop_fixed`, `Turing.MultiTapeTM.output_prefix`, `Turing.joinFields_cfgRecord_length`.
