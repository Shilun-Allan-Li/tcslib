<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_call_shape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shape of an Embedded Call Configuration

**Claim.** Under the stated blank-tape and zero-head assumptions, embedding the hosted configuration with tag $b$ and empty prefix gives the trial configuration with the corresponding paired state, input position, buffers, output buffer, and virtual-head positions.

**Proof.** Compare the two configurations field by field. Their states and input positions agree directly from the definitions. For tape contents, the embedded buffer tape maps to the trial buffer slot, where both store $y$; the other embedded tapes are blank by the hypothesis on $c$, and their trial slots are blank as well. The separate prefix buffer stores $u$, while the capture tape stores the output of $c$; the latter is disjoint from the embedding image by the assumption on the capture index. Every remaining tape retains the trial configuration's specified contents. For head positions, the embedded buffer head is at the shifted virtual input position, as required by the trial configuration, and the other embedded heads are at zero by hypothesis. The capture head is at $|c.output|$, and all other heads retain their specified zero positions. The zero-time framing fact (`Turing.embedSilentTM_frame`), together with the selected-tape and selected-head identities (`Turing.embedSilentCfg_selected_tape`, `Turing.embedSilentCfg_selected_pos`) and the capture-tape identities (`Turing.embedSilentCfg_cap`), supplies the corresponding equalities for these cases. Thus all configuration fields agree.

**Key facts.** `Turing.embedSilentCfg_selected_tape`, `Turing.embedSilentCfg_cap`, `Turing.embedSilentTM_frame`, `Turing.embedSilentCfg_selected_pos`.
