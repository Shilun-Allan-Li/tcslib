<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.NDTM.mapOutput_stepWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Mapping Commutes with One Step

**Claim.** Taking one step in the machine with transition outputs mapped by $f$, from a configuration whose output is mapped by $f$, yields the configuration obtained by taking one step in the original machine and then mapping its output.

**Proof.** Split according to whether the configuration is halted. If its state is none, both machines leave the configuration unchanged, by the fact that a halted machine takes no step (`Turing.NDTM.stepWith_of_halt`); mapping the output does not alter the state. If its state is some $q$, mapping the configuration leaves its state, input symbol, and work-tape symbols unchanged, so both machines consult the same transition, indexed by $b$ and $q$. Their resulting configurations therefore agree in state, head positions, and work-tape contents and positions. For the output, the mapped configuration's prior output is the original output filtered by $f$, and the mapped transition appends the transition's emitted symbol after applying $f$. Filtering a concatenation distributes over its two parts. If the transition emits no symbol, both appended contributions are empty; if it emits $v$, both contributions are the one-element word containing $f(v)$ when defined, and empty otherwise. Thus the outputs also agree.

**Key facts.** `Turing.NDTM.stepWith_of_halt`.
