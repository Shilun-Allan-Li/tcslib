<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.Cfg.liftOver_inputPos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Head Position Under Lifting

**Claim.** For an injection $e$ from Boolean symbols into $\Gamma$, equal-length inputs $x$ and $x'$, and configurations $D$ on $x$ and $c$ on $x'$, the lifted configuration has the same numerical input-head position as $c$.

**Proof.** By definition, the input-head position of the lifted configuration is obtained from the input-head position of $c$ by transporting it to the matching finite type for the input length of $x$. This transport changes only the bound witnessing that the position is in range, not its numerical value. Hence the two numerical positions are equal.
