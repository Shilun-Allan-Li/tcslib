<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.runFrom_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step run

**Claim.** After one step, a machine's run from a configuration is exactly the one-step successor of that configuration.

**Proof.** A run for one step is the first iterate of the machine's step function. By the definition of iteration, this is precisely one application of the step function to the starting configuration.
