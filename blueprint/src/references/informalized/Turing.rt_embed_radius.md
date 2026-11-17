<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_embed_radius -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head-radius bound under tape embedding

**Claim.** If every head of the original machine stays within distance $B$ of its initial position through time $t$, then the embedded machine’s heads satisfy the same bound through that time.

**Proof.** Fix a time $u\le t$ and a tape index $j$ in the larger machine. If $j=\iota(i)$ for some original tape index $i$, the run-embedding identity (`embedEmitTM_runFrom`) identifies the embedded run with the embedding of the original run. The selected-position identity (`embedEmitCfg_selected_pos`) identifies the initial head position at this tape with the original head position, so the assumed radius bound for tape $i$ gives the result. If $j$ is outside the image, the frame property (`embedEmitTM_frame`) says that its head stays at its chosen initial position at every time. Its displacement is therefore zero, which is at most $B$ because $B\ge0$.

**Key facts.** `Turing.embedEmitTM_runFrom`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitTM_frame`.
