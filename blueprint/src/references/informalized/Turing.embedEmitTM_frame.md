<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitTM_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frame Preservation Under Tape Embedding

**Claim.** After any number of steps of the embedded machine, each unselected tape retains its supplied contents and head position, while the input-head position and output agree with the original run, with the given prefix prepended to the output.

**Proof.** First use `Turing.embedEmitTM_runFrom` to identify the entire run of the embedded machine with the embedding of the original machine's run. For any index $j$ outside the embedding's image, `Turing.embedSlot_unselected` says the slot search returns no original tape index. Thus the embedding supplies exactly the given tape contents and head position at $j$. The input-head position is copied unchanged by the embedding, and its output is the fixed prefix followed by the original output, so these fields give the other two conclusions.

**Key facts.** `Turing.embedEmitTM_runFrom`, `Turing.embedSlot_unselected`.
