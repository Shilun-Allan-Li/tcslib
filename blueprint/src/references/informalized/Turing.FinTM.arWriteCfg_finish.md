<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arWriteCfg_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finishing the write sweep

**Claim.** One simulator step from the counter-zero write-sweep configuration is the move-sweep configuration at counter $N+1$, for the same configuration and action.

**Proof.** At counter zero, the simulator is in the branch that writes offset zero. The resulting control state and input position match those of the claimed move-sweep configuration by their definitions. For each work tape, the single transition writes the first encoded entry at the current head position. The write-cell update lemma (`arTail_update`) identifies this operation with lowering the sweep counter from one to zero; the initial-family lemma (`arTail_zero`) identifies the resulting family with the encoding of the tape obtained by applying the action's pointwise write. The action's work-tape update formula (`Action.apply_workTapes`) says that this is exactly the work tape in the action-applied configuration used by the move-sweep configuration. Finally, the head positions agree by their definitions, and the output fields agree by the definitions of the action application and the two configurations. Thus every configuration field matches.

**Key facts.** `Turing.FinTM.arTail_update`, `Turing.FinTM.arTail_zero`, `Turing.Action.apply_workTapes`.
