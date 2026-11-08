<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_origin_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Rewind Computation

**Claim.** The embedded virtual-input rewind machine reaches its halting-return configuration at some time, without entering that return state earlier; through that time the selected tape head remains between $-1$ and $|y|$, and all other work-tape heads remain at zero.

**Proof.** Take the auxiliary zero-work-tape rewind configuration on input $y$ with its head at the right boundary, and pair it with the true virtual-input tag. The virtual-host rewind result (`Complexity.b2b_vhost_rewind`) gives a run ending in a halted auxiliary configuration at the left boundary, with the stored buffer restored and its head at zero. The embedding-shape identity (`Complexity.b2b_origin_shape`) identifies its initial embedding with the specified starting configuration, and identifies the embedded terminal configuration with the desired tape contents and head position. Choose the first halting time of the auxiliary run, using the first-halt principle (`Turing.MultiTapeTM.exists_first_halt`); this preserves the same terminal configuration and ensures the auxiliary machine is live at every earlier time. The embedding simulation theorem (`Turing.embedEmitRetTM_run`) then matches the embedded run to the auxiliary run before that time and gives the return state exactly at the chosen time. For the head bounds, the selected embedded tape head agrees with the virtual buffer head (`Turing.embedEmitCfg_selected_pos`), which stays in $[-1,|y|]$ by the virtual-host head bound (`Turing.vhostCfg_buffer_head_mem`). Every unselected tape retains its initial head position zero by the embedding frame property (`Turing.embedEmitTM_frame`).

**Key facts.** `Complexity.b2b_vhost_rewind`, `Turing.MultiTapeTM.exists_first_halt`, `Turing.embedEmitRetTM_run`, `Complexity.b2b_origin_shape`, `Turing.embedEmitCfg_selected_pos`, `Turing.vhostCfg_buffer_head_mem`, `Turing.embedEmitTM_frame`.
