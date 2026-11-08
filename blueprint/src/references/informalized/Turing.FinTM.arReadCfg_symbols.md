<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arReadCfg_symbols -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symbols Scanned During the Read Sweep

**Claim.** At a valid read-sweep counter $j<N+1$, each encoded work head scans the entry at offset $j$ in the block code of the symbol scanned by the corresponding original work head.

**Proof.** Fix a work tape. Its encoded head position is $(N+1)z+j$, where $z$ is the original head position. Evaluating the encoded tape at this position selects block coordinate $z$ and offset $j$, by the tape-at-position identity (`Turing.FinTM.arTape_at`). The encoded tape at block $z$ is the code of the original tape contents there. Thus the scanned entry is the offset-$j$ entry of the code of the original scanned symbol. This holds for every work tape, so the functions of scanned symbols agree.

**Key facts.** `Turing.FinTM.arTape_at`.
