<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_state_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Five-Step State Scan

**Claim.** Starting at the record-step entry state with the one-symbol state record on tape 0, the record-step machine takes five steps to the running phase that skips this symbol and stores the decoded optional state $q$ in its record data. Neither verdict state is reached earlier, and every work head stays within distance one of its initial position.

**Proof.** View the initial configuration as a forward scan configuration with accumulator `none`. The forward scan over the one-symbol word `[st q]` returns accumulator $q$ and leaves the word unchanged, by the fold description of the scan result (`scanResult_fold`). The scan-run theorem (`scanTM_run_ofCfg`) therefore gives the scan's completed state after $2\cdot1+2=4$ steps, with the tape restored and all head positions within the one-cell bound. The phase-host transition theorem (`phaseHostTM_run`) adds one control transition from this completed scan state to the state-skip running phase, since the phase router sends this completion to that phase. Its earlier-transition condition holds because the scan has no completed state before its terminal step. The entry-state hypothesis identifies the scan configuration with the original configuration, and the resulting state is exactly the claimed record data. Finally, the bounded-run packaging lemma (`recordRun_tagged`) combines the four scan steps and the control transition, including the exclusion of both verdict states and the head bound.

**Key facts.** `Turing.scanResult_fold`, `Turing.scanTM_run_ofCfg`, `Turing.phaseHostTM_run`, `Turing.recordRun_tagged`.
