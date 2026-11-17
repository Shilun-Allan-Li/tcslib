<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldCfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step folding simulation

**Claim.** One step of the folding simulator from the folded configuration of $c$ equals the folded configuration obtained by taking one step of the original machine from $c$.

**Proof.** Split according to whether the original machine is halted. If its state is absent, the original step leaves $c$ unchanged, and folding its absent state again gives the same folded configuration. If its state is $q$, the folded state records $q$ together with the side of each original work-tape head. The input-symbol correspondence says that the folded input read is the embedded original input symbol (`foldCfg_input`). For each work tape, reading the folded symbol on the recorded side recovers exactly the original symbol under the head (`foldRead_tape`). Now split according to whether the original input symbol is absent or is some symbol $a$. In either case the folded transition receives the same input and work-tape symbols as the original transition, with the input symbol embedded when present. The action-translation correspondence then shows that applying the translated action to the folded configuration is exactly the fold of applying the original action (`foldCfg_apply`). This gives the required equality in both input cases.

**Key facts.** `Turing.FinTM.foldCfg_input`, `Turing.FinTM.foldRead_tape`, `Turing.FinTM.foldCfg_apply`.
