<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.Traj.segment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trajectory property gives a computation segment

**Claim.** For any admissible datum and starting configuration, the contract run reaches its endpoint, avoids the exit set at every earlier time, and satisfies the trajectory property through the endpoint time.

**Proof.** A segment consists of three assertions: the run at the contract time equals the endpoint; every earlier run state lies outside the exit set; and the trajectory predicate holds at each time up to and including the contract time. These are exactly the contract's run and cut properties and the assumed trajectory property, respectively, applied to the given datum and starting configuration.
