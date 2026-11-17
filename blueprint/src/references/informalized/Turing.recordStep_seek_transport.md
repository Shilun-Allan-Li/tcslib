<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_seek_transport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transport of a Bounded Seek Computation

**Claim.** A bounded seek run on Boolean tapes transports to the embedded record-symbol machine with the same first arrival time, head-displacement bound, and terminal configuration, with input-head position $p$.

**Proof.** Decode the two selected embedded tapes to form a Boolean two-tape configuration. The buffer decoding identity (`FinTM.bufferTape_map_decode`) verifies the first tape's word hypothesis, and the blank-tape hypothesis verifies the second. Apply the assumed seek specification to obtain a first arrival time, the head bounds, and preservation of both tapes, both heads, and output, with input position $p$. The simulated terminal configuration is therefore the decoded starting configuration with just the state and input position changed. The run-transport identity (`recordStep_transport`) carries the Boolean computation to the symbol-lifted computation on the embedded tapes; the digit-symbol hypothesis ensures every selected-tape symbol decodes. For head bounds on selected tapes, the selected-position identity (`embedEmitCfg_selected_pos`) identifies their head locations with the simulated heads. For unselected tapes, the embedding frame property (`embedEmitTM_frame`) says their heads remain fixed, so their displacement is zero. At the terminal time, transport and the simulated terminal identity show that all tapes, heads, and output return to their original values, while the state and input position have the specified values.

**Key facts.** `Turing.FinTM.bufferTape_map_decode`, `Turing.recordStep_transport`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitTM_frame`.
