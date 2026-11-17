<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilentCfg_selected_tape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tape contents under embedding

**Claim.** For every original tape index $i$, the contents on tape $\iota(i)$ in the embedded configuration equal the contents on tape $i$ in $c$.

**Proof.** At the selected index $\iota(i)$, the slot lookup returns $i$ by the selected-slot property (`Turing.embedSlot_selected`). Therefore the embedded tape-content function takes its selected-tape branch and returns exactly $c$'s contents on tape $i$.

**Key facts.** `Turing.embedSlot_selected`.
