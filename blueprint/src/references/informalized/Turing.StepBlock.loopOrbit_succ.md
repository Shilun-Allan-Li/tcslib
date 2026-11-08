<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean :: Turing.StepBlock.loopOrbit_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Loop-Orbit Configurations

**Claim.** For every compiled-machine configuration $d$ and natural number $r$, the configuration after $r+1$ exit-delimited rounds is obtained by running the compiled machine from the configuration after $r$ rounds for exactly the duration assigned to that next round.

**Proof.** By definition, the loop orbit is the $r$-fold iterate of the map sending a configuration $c$ to the result of running the round machine for $[?]$ (namely, $[?]$) steps. The successor law for round orbits states that the $(r+1)$st iterate is one more application of this map to the $r$th iterate: run the machine from that intermediate configuration for its assigned duration. Applying this law with the round machine and its duration function gives the claim.

**Key facts.** `Turing.roundOrbit_succ`.
