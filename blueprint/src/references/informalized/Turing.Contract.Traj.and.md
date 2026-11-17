<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.Traj.and -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conjunction of Trajectory Properties

**Claim.** If two properties each hold at every time up to and including a contract's duration, then their conjunction also holds at every such time.

**Proof.** Fix any permitted parameter, starting configuration, time, and work-head position vector. The two trajectory hypotheses give the first property and the second property at that same point. Hence both hold together, which is precisely their conjunction.
