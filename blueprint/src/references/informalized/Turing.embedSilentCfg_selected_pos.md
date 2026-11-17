<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilentCfg_selected_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head positions under embedding

**Claim.** For any original tape index $i$, the head position on tape $\iota(i)$ in the embedded silent configuration equals the head position on tape $i$ in $c$.

**Proof.** At the selected index $\iota(i)$, the slot lookup returns the original index $i$ (the selected-slot property, `Turing.embedSlot_selected`). Thus the embedded configuration uses its first branch for the head-position function, which assigns exactly $c$'s head position on tape $i$.

**Key facts.** `Turing.embedSlot_selected`.
