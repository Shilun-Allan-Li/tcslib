<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMatch_tick -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Live Clock Starts a Row Query

**Claim.** If $j<N$, one step from the matcher’s initial search control enters row-loading control at counter zero with the fresh-loader state, leaving the row, target words, stream, cursor, clock position, and flags unchanged.

**Proof.** The clock tape contains $N$ true symbols and its head is at position $j$. Since $j<N$, the scanned symbol is true, so the initial search branch selects the control action that enters row-loading control at counter zero with the fresh-loader state. This action has zero movement on every tape and writes and emits nothing. Consequently the tape contents and work-head positions remain fixed; the zero input movement also preserves the input-head position. The control-action behavior (`Turing.FinTM.controlAction_apply`) and the zero-movement identity (`Turing.moveInputPos_zero`) give the claimed configuration equality.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
