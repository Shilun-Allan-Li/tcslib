<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_find_skip_phase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement During a Skip Phase

**Claim.** During the skip phase, the host agrees with the standalone skip machine through the scan of the word, then redirects from the completed skip state to the prescribed combined state.

**Proof.** Apply the skip-machine run theorem (`Turing.skipTM_run_ofCfg`) to the given run state and tape contents. It says the standalone machine reaches `.done` after $|w|+1$ steps and has not reached `.done` at any earlier time. In particular, before that final time every state encountered is still `.run`: the skip machine has no other state reachable from the given initial state. The host’s redirect is therefore undefined at every such earlier state. The phase-host run theorem (`Turing.phaseHostTM_run`) now gives agreement with the standalone run at every time through $|w|+1$, with the control state tagged by phase $j$, and applies the specified redirect on the next step. The skip run theorem identifies the completed configuration: tape 0’s head has moved right by $|w|+1$, and the other configuration data are unchanged. The redirect changes only the state, so the resulting state is exactly the asserted configuration tagged by $q$.

**Key facts.** `Turing.skipTM_run_ofCfg`, `Turing.phaseHostTM_run`.
