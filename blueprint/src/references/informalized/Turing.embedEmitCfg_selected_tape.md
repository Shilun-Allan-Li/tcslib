<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitCfg_selected_tape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Selected Tape Contents

**Claim.** For every original tape index $i<m$, the embedded configuration has at tape $\iota(i)$ exactly the contents that tape $i$ has in $c$.

**Proof.** By the defining rule for the embedded configuration, the contents at an index $j$ are taken from the original configuration whenever the slot search identifies $j$ as an embedded index. The selected-slot fact `Turing.embedSlot_selected` says that at $j=\iota(i)$ this search returns precisely $i$. Substituting this into the definition gives the required equality of tape contents.

**Key facts.** `Turing.embedSlot_selected`.
