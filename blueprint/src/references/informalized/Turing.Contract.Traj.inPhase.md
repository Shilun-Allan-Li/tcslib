<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.Traj.inPhase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trajectory Property Within a Phase

**Claim.** If a contract for a phase machine satisfies a trajectory property, then the contract hosted in that phase satisfies the same property for the configuration with its state replaced by the phase entry state and with the same work-head positions.

**Proof.** Fix a run of the hosted contract and a time up to its duration. The hosted duration is the phase contract's duration plus one transition. If the chosen time is before that final transition, the run correspondence in the phase-host trajectory fact (Turing.Contract.inPhase_traj) identifies it with the phase machine's run, with states renamed into the host; head positions are unchanged. Applying the original trajectory property at that time proves the claim. At the final time, the run correspondence identifies the hosted configuration with the phase contract's endpoint after the extra transition. The original trajectory property applies at the endpoint time, since that time is included in the phase contract's duration. The extra transition changes the state through the reduction rule but leaves work-head positions unchanged, so the same property holds there as well.

**Key facts.** `Turing.Contract.inPhase_traj`.
