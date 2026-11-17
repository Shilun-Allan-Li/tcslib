<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean :: Complexity.LogProg.compile_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Compiled Simulation

**Claim.** Under the register-head bounds and the call conditions through time $N$, the compiled machine reaches the compiled configuration corresponding to the register-program run at time $N$, while preserving the register and decider-head bounds throughout the compiled run.

**Proof.** Apply the simulation theorem from an arbitrary initial configuration (`compile_correct_from`) to the initial register-program configuration. Its hypotheses are exactly the assumed bounds on the register heads and the assumed call conditions, and it yields a time at which the compiled machine, started from the seam of that initial configuration, reaches the seam of the register-program configuration at time $N$, with the bounds holding at every intervening time. The compiled machine’s initial configuration is precisely this seam by the initial-configuration identity (`seam_init`). Substituting that identity gives the claimed run from the compiled machine’s own initial configuration.

**Key facts.** `Complexity.LogProg.compile_correct_from`, `Complexity.LogProg.seam_init`.
