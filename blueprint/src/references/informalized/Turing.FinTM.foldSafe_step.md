<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldSafe_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Simulator Safety

**Claim.** If a configuration of the folding simulator satisfies the safety invariant, then the configuration after one simulator step satisfies it as well.

**Proof.** Split according to the current state. If the state is halting, the machine leaves the configuration unchanged, so safety persists. Otherwise the state cannot be the fresh initial state, by the safety hypothesis; thus it has the form consisting of an original machine state together with a side choice for each work tape. Now split according to the current input symbol. If it is absent, the simulator applies the folded version of the original machine's transition. If it is present, split according to whether it decodes: a decoding failure makes the simulator halt, while a successful decode again applies the folded original transition. The safety lemma for folded transitions (`foldAction_safe`) preserves the invariant in the transition cases, and the safety lemma for halting (`foldHalt_safe`) handles the decoding-failure case. Hence every possible step preserves safety.

**Key facts.** `Turing.FinTM.foldAction_safe`, `Turing.FinTM.foldHalt_safe`.
