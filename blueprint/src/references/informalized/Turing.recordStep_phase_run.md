<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_phase_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Hosted Phase Transition

**Claim.** Under the stated row-run, transition, cutoff, and head-radius hypotheses, the hosted record-step machine performs the phase transition in $t+1$ steps, avoids both verdict states before its final time, and stays within the specified head radius.

**Proof.** Apply the phase-host simulation theorem `phaseHostTM_run` to the row machine indexed by $i$. The cutoff hypothesis ensures that before time $t$ the host follows this row rather than redirecting early. Up to time $t$, the hosted run is therefore the row run with phase index $i$ attached; at the next step, the specified transition outcome redirects it to the configuration with state replaced by $o$.

The row index is not either verdict index, by the hypothesis excluding verdict stages. Hence none of the intermediate hosted states can be a verdict state. The row's head-radius bound applies through time $t$, and the endpoint at time $t+1$ has the same work-head positions as the row endpoint, so it also satisfies that bound. Together these facts give the required `RecordRun`.

**Key facts.** `Turing.phaseHostTM_run`, `Turing.recordRun_tagged`.
