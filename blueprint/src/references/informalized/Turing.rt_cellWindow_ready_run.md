<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_cellWindow_ready_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ready-State Cell-Window Computation

**Claim.** Under the stated ready configuration hypotheses, the embedded machine reaches its designated done state within $18(s+|ws|)+32$ steps, avoids that state earlier, and keeps every head within distance $2s+|ws|+3$ of its initial position. At that time only the specified interval of tape $\iota(1)$ has been replaced by the centered buffer of cell symbols.

**Proof.** First construct a three-tape Boolean configuration whose tape 0 contains $ws$, whose other tapes are blank, and whose heads and input position match the three embedded tapes of $d$. The tape-bank hypothesis guarantees that, on each selected tape, embedding this configuration reproduces $d$; on tape 0, this uses the fact that mapping symbols through the Boolean embedding commutes with the buffer construction (`FinTM.bufferTape_map`). The general embedding agreement theorem (`rt_embed_matches`) then shows that embedding this constructed configuration, with the given surrounding tapes, heads, and output, recovers exactly $d$. Apply the embedded cell-window computation theorem (`rt_cellWindow_embed_run`) to obtain the time bound, earlier-state avoidance, head-radius bound, and the final embedded configuration. The same embedding agreement theorem identifies that final configuration with the stated update of $d$: the selected tape receives the centered cell buffer, while all other tape contents and configuration fields retain their values.

**Key facts.** `Turing.FinTM.bufferTape_map`, `Turing.rt_embed_matches`, `Turing.rt_cellWindow_embed_run`, `Turing.rt_embed_matches`.
