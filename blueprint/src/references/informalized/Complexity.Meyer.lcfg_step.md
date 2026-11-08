<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineRun.lean :: Complexity.Meyer.lcfg_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step lifted configuration identity

**Claim.** The simulator's one-step successor of the lifted configuration is its transition action applied at that configuration, with the transition supplied the scanned input symbol and the symbols under all original and auxiliary work-tape heads.

**Proof.** Apply the tabulated machine's one-step identity (`tabTM_step`) to the lifted configuration. Its work-symbol tuple consists of the original work-tape symbols followed by the three auxiliary-tape symbols at their heads. The original entries agree with the configuration's work-tape symbols by their definition. The first auxiliary tape stores the input word in buffered form, with head at the original input-head position shifted by one; the buffered tape therefore returns exactly the original scanned input symbol (`bufferTape_inputSymbol`). The other two auxiliary entries are, by construction, the contents of their respective tapes at their head positions. Thus the transition receives precisely the tuple in the claimed identity, and the one-step configurations agree.

**Key facts.** `Complexity.Meyer.tabTM_step`, `Turing.FinTM.bufferTape_inputSymbol`.
