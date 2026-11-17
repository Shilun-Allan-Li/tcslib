<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.roundOrbit_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Orbit Rounds

**Claim.** The configuration after $r+1$ rounds is obtained by running the machine for the prescribed number of steps from the configuration after $r$ rounds.

**Proof.** The orbit is the $r$-fold iterate of the map sending a configuration $c$ to the result of running the machine from $c$ for $$ of its rounds. The successor formula for function iteration says that the $(r+1)$-fold iterate is one more application of this map to the $r$-fold iterate. Substituting the definition of the map gives the stated equality.
