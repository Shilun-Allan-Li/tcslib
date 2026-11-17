<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_lenParse_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the First Bit of a Block

**Claim.** For $x=\mathrm{pre}\,b\,\mathrm{rest}$, one step from the pair-reading state at the beginning of the block records $b$ in the parser state and advances the input head by one position.

**Proof.** The input-symbol formula for the length-counting configuration says that its head at position $|\mathrm{pre}|+1$ scans the symbol at index $|\mathrm{pre}|$ (`f2_lenCfg_read`). The decomposition of $x$ identifies this symbol as $b$. In the pair-reading state with no bit yet recorded, the transition rule stores $b$ in the parser state and makes a positive input move, without changing the extra-tape head or emitting output. Since this position is not the right boundary, the positive move advances the shifted head position by one (`moveInputPos_pos_of_ne_right`). The resulting configuration is therefore the claimed one (`f2_lenAction_apply`).

**Key facts.** `Turing.FinTM.f2_lenCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.f2_lenAction_apply`.
