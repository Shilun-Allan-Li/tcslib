<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonGuardBlock_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Guard Block

**Claim.** For every machine format $F$, the guard-block bound is positive.

**Proof.** The quantity $(4F.k+5)3^{F.k+1}$ is positive: both factors are positive natural numbers. The guard block is the maximum of this quantity and $F.guard$, so it is at least this positive quantity and hence is positive.
