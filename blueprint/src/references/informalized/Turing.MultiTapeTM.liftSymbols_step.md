<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.MultiTapeTM.liftSymbols_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting a Single Computation Step

**Claim.** For every Boolean input word and configuration, one step of the symbol-lifted machine from the lifted configuration is the lift of the original machine’s one-step result.

**Proof.** Split according to whether the configuration is already halted. If its state is empty, both machines leave the configuration unchanged, so the two sides agree. Otherwise write its state as $q$. The lifted configuration reads the image under $e$ of the original input symbol; the fact that decoding this lifted symbol recovers the original one is supplied by the input-symbol lifting identity (`Turing.Cfg.liftSymbols_inputSymbol`). At each work-tape head, decoding the lifted tape symbol likewise recovers the original symbol, including when that cell is blank. Thus the lifted transition is exactly the lift of the original transition at the same state and read symbols. Compare the resulting configurations field by field: the state and output agree directly; the input-head positions agree because moving a cast position is compatible with the cast (`Turing.moveInputPos_cast`); and on each work tape the write action either leaves the tape unchanged or writes the image of the same symbol at the same head position. The head positions therefore agree as well, proving equality of configurations.

**Key facts.** `Turing.Cfg.liftSymbols_inputSymbol`, `Turing.moveInputPos_cast`.
