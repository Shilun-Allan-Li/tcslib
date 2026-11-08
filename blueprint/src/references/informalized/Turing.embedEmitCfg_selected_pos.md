<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitCfg_selected_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Selected Head Positions

**Claim.** After embedding an $m$-tape configuration, the head position on tape $\iota(i)$ equals the head position on tape $i$ in the original configuration.

**Proof.** For a selected index $\iota(i)$, the slot lookup identifies it with $i$ (`Turing.embedSlot_selected`). By the definition of the embedding, the head position at that selected slot is therefore the original head position on tape $i$.

**Key facts.** `Turing.embedSlot_selected`.
