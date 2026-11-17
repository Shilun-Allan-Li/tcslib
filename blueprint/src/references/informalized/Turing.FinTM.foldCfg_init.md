<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldCfg_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initialization of the Folded Configuration

**Claim.** For a finite alphabet with decidable equality, one step of the folding simulator from its initial configuration on the embedded input produces the folded initial configuration of the original machine.

**Proof.** The simulator begins in its special start state. Its input symbol is the embedded version of the original machine's initial input symbol, as expressed by the folded-input identity (`foldCfg_input`). The start transition on an embedded symbol is the initialization action (`foldStartAction_embed`): it enters the original initial state with all fold sides set to the positive side and initializes each folded tape with its origin marker. Compare the resulting configuration with the fold of the original initial configuration. Their states, input-head positions, and outputs agree by construction. On each work tape, the initialized origin marker and blank contents match the folding of the originally blank tape, and the folded head position is the fold of the original head position $0$. Therefore all components coincide.

**Key facts.** `Turing.FinTM.foldCfg_input`, `Turing.FinTM.foldStartAction_embed`.
