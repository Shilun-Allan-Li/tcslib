<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.extract_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First step of the pair extractor

**Claim.** From the block-start configuration, one transition reads $b$, advances the input head by one position, and enters the control state recording $b$, leaving the work tape and output unchanged.

**Proof.** The input-reading lemma (`Turing.FinTM.extractCfg_read`) identifies the scanned symbol with $x[|pre|]?$. The decomposition $x=pre\mathbin{++}[b]\mathbin{++}rest$ makes this symbol $b$. The extractor's block-start transition therefore records $b$ in its control state, moves the input head one place to the right, and makes no work-tape or output change. The positive input-movement fact (`Turing.moveInputPos_pos_of_ne_right`) gives the new shifted position corresponding to $|pre|+1$, so the resulting configuration is the one claimed.

**Key facts.** `Turing.FinTM.extractCfg_read`, `Turing.moveInputPos_pos_of_ne_right`.
