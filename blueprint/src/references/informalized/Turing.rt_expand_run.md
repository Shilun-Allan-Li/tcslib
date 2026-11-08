<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_expand_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Expanded-Machine Execution

**Claim.** Starting with the specified counter state and binary counter word, the expanded machine completes exactly after the stated number of steps, writes the repeated pattern and the all-true counter interval, avoids its done state earlier, and obeys the head-displacement bound.

**Proof.** First represent the given three-tape configuration as a counter-loop configuration: the first two tapes form the body machine's configuration, and the third tape is the separate counter tape. The counter-configuration identity (`counter_cfg_eq`) verifies this decomposition, including the initial state and tape contents. Apply the expanded-machine run theorem (`expandTM_run_ofCfg`) to the body that writes one copy of the pattern per counter unit. Its conclusion gives the exact final body tape, counter tape, head position, and state, as well as the time bound, the fact that the done state is not reached earlier, and bounds on the body and counter heads throughout the run. The initial counter-buffer hypothesis supplies its tape precondition, and the digit-value hypothesis supplies the numerical counter value. Reassemble the two configurations using the counter-configuration identity; the first body tape is unchanged, the second has advanced by the length of the repeated pattern, and the counter tape's head remains within its specified interval. The resulting configuration and head bound are precisely those asserted.

**Key facts.** `Turing.counter_cfg_eq`, `Turing.expandTM_run_ofCfg`.
