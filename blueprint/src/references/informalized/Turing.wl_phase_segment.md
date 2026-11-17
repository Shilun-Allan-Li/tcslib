<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.wl_phase_segment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hosted Phase Segment

**Claim.** A row-machine run that first reaches a state admitting a phase transition is simulated by the hosted machine for the same number of steps, followed by one transition to the corresponding hosted state. The hosted run avoids stop-phase states before that endpoint, and the head-position predicate holds throughout the segment.

**Proof.** Apply the phase-host simulation lemma (\texttt{Turing.phaseHostTM\_run}) to the row run. Its guard hypothesis ensures that at each time strictly before $t$, the hosted machine follows the row machine with its phase embedded in the control state. At time $t+1$, the reduction rule takes the hosted machine from the embedded endpoint state to $q$, so the endpoint is the stated configuration. For any earlier time, the simulated state still has phase index $i$; since $i\ne\mathrm{stop}$, it cannot be a stop-phase state. For the position predicate, at times through $t$ the hosted and row configurations have identical head positions, so the assumed bound applies. At time $t+1$, the transition changes only the control state and leaves head positions unchanged; the bound at time $t$ therefore also gives the endpoint bound.

**Key facts.** `Turing.phaseHostTM_run`.
