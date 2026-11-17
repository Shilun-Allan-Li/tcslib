<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean :: Turing.StepBlock.loopOrbit_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Loop-Orbit Configurations

**Claim.** For every compiled-machine configuration $d$ and natural number $r$, the configuration after $r+1$ exit-delimited rounds is obtained by running the compiled machine from the configuration after $r$ rounds for exactly the duration assigned to that next round.

**Proof.** By the definition of counterLoopOrbit and the successor law for round orbits, the $(r+1)$-round configuration is obtained by running the round machine from the $r$-round configuration for the duration assigned to that configuration. This is exactly the stated equation.

**Key facts.** `Turing.roundOrbit_succ`.
