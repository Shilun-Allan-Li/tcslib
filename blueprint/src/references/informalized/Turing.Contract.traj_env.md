<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.traj_env -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trajectory Within the Head Envelope

**Claim.** Every work-tape head position along an admissible run, through the contract's running time, lies between its corresponding lower and upper bounds.

**Proof.** Fix an admissible parameter and starting configuration, a time within the contract's running time, and a work-tape index. The contract's envelope property directly places that head position in the interval from the corresponding lower bound to the upper bound. This is precisely the asserted trajectory property.
