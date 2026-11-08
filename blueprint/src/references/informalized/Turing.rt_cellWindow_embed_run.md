<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_cellWindow_embed_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Cell-Window Computation

**Claim.** Under the stated initial buffer and blank-cell hypotheses, the embedded machine reaches its designated done state by time $18(s+|ws|)+32$, avoids that state at earlier times, and keeps every work-tape head within distance $2s+|ws|+3$ of its starting position. At that time, the embedded configuration has the prescribed centered cell buffer on tape $\iota(1)$, with the output prefix preserved.

**Proof.** Apply the three-tape cell-window run theorem to the original configuration $a$. It supplies a time $t$ with the stated cost bound, the earlier-state avoidance, the head-radius bound, and the precise final configuration for the computation after lifting Boolean symbols into the digit alphabet and adjoining the state tag. The embedding theorem for runs (`embedEmitTM_runFrom`) identifies the run of the embedded machine from the configuration built using the surrounding tapes, heads, and output prefix with the embedding of that three-tape run. Consequently the same time and state-avoidance bound hold for the embedded computation. The embedding radius theorem (`rt_embed_radius`) transfers the three-tape head bound to every tape of the larger machine, including the unchanged surrounding tapes. Finally, embedding the three-tape final configuration gives the asserted final tape contents and state; because the original output is empty, the embedded output is exactly the supplied prefix.

**Key facts.** `Turing.rt_cellWindow_run`, `Turing.embedEmitTM_runFrom`, `Turing.rt_embed_radius`.
