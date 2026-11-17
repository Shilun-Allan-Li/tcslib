<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_clean_capture -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Captured Clean Computation

**Claim.** Under the stated halting and space bounds, the embedded return machine reaches a return configuration with output $y$ and some input-head position. Before that time it has not returned; through that time it is live and its output is empty. The reserved tape head stays between $0$ and $|y|$, selected tape heads stay within distance $s$ of the origin, and all other heads remain at their background positions.

**Proof.** First apply the clean simulation result (`Complexity.b2b_clean_run`) to obtain a clean machine run that halts with output $y$, has all work tapes blank and heads at the origin at its endpoint, and keeps every head within distance $s$ throughout. Let $T_0$ be that endpoint. The clean machine may already have halted before $T_0$, so choose its first halting time $T\leq T_0$ (`Turing.MultiTapeTM.exists_first_halt`). Its configuration at $T$ equals the one at $T_0$; in particular, it has output $y$ and the same tape contents and head positions. The run is live at every earlier time.

Embed this run into the larger machine using the return-machine simulation theorem (`Turing.embedSilentRetTM_run`). Before the embedded machine's return step, its configurations are exactly the embedded clean configurations; at time $T$, the clean machine's halt is converted into the return state. Thus the embedded run has not returned earlier and has the claimed final configuration. It remains live through the return time, and its output stays empty because the return embedding stores emitted symbols on the reserved tape rather than on the output tape.

For the reserved tape, the embedding places its head at the length of the captured output prefix. Output prefixes grow monotonically (`Turing.MultiTapeTM.output_prefix`), so through time $T$ this length lies between $0$ and the final length $|y|$. For a tape in the image of the embedding, its head position is the corresponding clean-machine head position (`Turing.embedSilentCfg_selected_pos`), hence satisfies the space bound. For any other tape distinct from the reserved one, the embedding frame property keeps its head at its prescribed background position (`Turing.embedSilentTM_frame`).

**Key facts.** `Complexity.b2b_clean_run`, `Turing.MultiTapeTM.exists_first_halt`, `Turing.embedSilentRetTM_run`, `Turing.MultiTapeTM.output_prefix`, `Turing.embedSilentCfg_selected_pos`, `Turing.embedSilentTM_frame`.
