<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.NDTM.mapOutput_initCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration and Output Mapping

**Claim.** Mapping the output of the initial configuration by $f$ gives the initial configuration of the machine whose transition outputs are mapped by $f$.

**Proof.** The initial configuration has output the empty word. Filtering that output through the partial map $f$ still gives the empty word, while the state, input-head position, work tapes, and work-head positions are unchanged. The mapped machine has the same initial state as the original machine, so its initial configuration agrees in every component with the mapped original initial configuration.
