<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.Cfg.liftSymbols_inputSymbol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scanned Symbol Under Symbol Lifting

**Claim.** After lifting a Boolean configuration through the embedding, the symbol scanned by the input head is the image of the original scanned symbol, and absence of a scanned symbol is preserved.

**Proof.** The lifted head position has the same numerical value as the original head position, and the lifted input has the same length as the original input. Consequently the head is at the left boundary for the lifted configuration exactly when it is at the left boundary originally, and likewise for the right boundary. In either boundary case both scanned-symbol values are absent. Otherwise both configurations select the list entry at the same zero-based position; mapping the input list through the embedding maps that entry to its image. Hence the scanned symbol after lifting is the image of the original scanned symbol, including the absent case.
