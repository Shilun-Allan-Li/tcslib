<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPlacedCfg_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Formula for a placed configuration

**Claim.** A placed configuration maps the source state and preserves its input-head position and output. Each occupied host tape receives the contents and head position of its selected source tape; each unoccupied host tape retains the supplied contents and head position.

**Proof.** Fix a host tape index $j$. If the selector chooses a source index $i$, exactness of the placement says that $j$ is the image of $i$. The embedded configuration therefore has the contents and head position of source tape $i$ there, by the selected-tape and selected-position properties (`Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`). If the selector chooses no source index, then $j$ lies outside the placement's image; the frame property of the embedded machine at time zero (`Turing.embedEmitTM_frame`) says that the supplied host contents and head position remain there. Thus both tape functions have the claimed values at every $j$. The state is mapped by the state map, the input-head position is unchanged, and the empty-prefix embedding preserves the output, yielding the formula.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitTM_frame`.
