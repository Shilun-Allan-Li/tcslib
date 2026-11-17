<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_restrict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction to Embedded Boolean Tapes

**Claim.** If every symbol on each selected tape lies in the image of the Boolean embedding, then the configuration is exactly the embedding of its decoded Boolean configuration on those tapes, with the other tapes and head positions framed by the original configuration and its output as prefix.

**Proof.** Define a Boolean configuration $c$ with the same state and input position as $d$, decoded contents on each selected tape, the corresponding selected head positions, and empty output. On a selected tape, compare the original cell content with its decoded-and-reembedded content. A blank remains blank; if the cell contains a symbol, the hypothesis supplies a Boolean preimage, and decoding that embedded bit returns the bit (`decodeBool_apply`). Thus the selected tape functions agree. The selected head positions agree by the selected-position property of tape embedding (`embedEmitCfg_selected_pos`). For every unselected tape, the frame property of the embedding says its tape contents and head position remain those of $d$ (`embedEmitTM_frame`). Finally, lifting $c$ embeds its output, which is empty, and the embedding construction prefixes it by $d$'s output; the state and input position are unchanged. Extensionality of configurations now gives the asserted equality.

**Key facts.** `Turing.decodeBool_apply`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitTM_frame`.
