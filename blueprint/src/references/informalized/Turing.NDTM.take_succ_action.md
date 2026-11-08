<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.NDTM.take_succ_action -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Additional Run Step

**Claim.** For every choice word and every natural number $j$, running on the prefix of length $j+1$ either gives the same configuration as running on the prefix of length $j$, or applies one action to the latter configuration.

**Proof.** Split the prefix of length $j+1$ into the prefix of length $j$ followed by the possible next bit. If that bit is absent, the two prefixes coincide, giving the first alternative. If it is a bit $b$, the run on the longer prefix first runs on the length-$j$ prefix and then takes one step with choice $b$. The run can be viewed as the corresponding fixed-choice machine (`stepWith_eq_fixChoice_step`). If the intermediate configuration is halted, the step leaves it unchanged, so the two runs coincide. Otherwise its state is some $q$, and the fixed-choice step is exactly the action selected by the transition function at $b$, $q$, and the symbols currently scanned. Thus the longer run is obtained by applying that action to the shorter run’s configuration. The decomposition of a run over concatenated choice words is given by `runWith_append`, with `runWith_cons` and `runWith_nil` identifying the added step and the empty suffix.

**Key facts.** `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_nil`, `Turing.NDTM.stepWith_eq_fixChoice_step`.
