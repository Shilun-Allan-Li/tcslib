<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.recordSkipTM_fixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-Width Recording and Skip Run

**Claim.** Starting in the recording machine’s initial state with the specified record bits on the table tape, after each $u\le 4k+4$ steps the renamed configuration is the one that has read the first $u$ bits; after $4k+5$ steps it is at the full-width read configuration in the tagged successor phase.

**Proof.** The recording machine’s run theorem says that, for every $u\le 4k+4$, its configuration after $u$ steps is the prescribed read configuration (`Turing.StepBlock.recordTM_read`). The phase-host run theorem transfers this run to the recording-and-skip machine while the phase reduction has not yet triggered. The guard needed for that transfer follows from the read-state description: before the full width is reached, the recorded position is strictly less than $4k+4$, so the reduction condition is false. At full width the reduction sends the recording phase to the successor phase’s tag state. The phase-host theorem then identifies the configuration one step later with the full-width read configuration carrying that tag (`Turing.phaseHostTM_run`). Combining these gives both parts of the claim.

**Key facts.** `Turing.StepBlock.recordTM_read`, `Turing.phaseHostTM_run`.
