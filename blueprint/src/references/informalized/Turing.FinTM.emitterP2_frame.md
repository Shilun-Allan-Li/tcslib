<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Framed Configuration Embedding

**Claim.** Under the stated agreement of states, input positions, outputs, selected tapes, and the ambient data on unselected tapes, embedding the source configuration with empty output prefix and mapping its state by $e$ gives exactly the host configuration.

**Proof.** Fix a host tape slot $j$. If $j$ lies in the image of the embedding, write $j=\iota(i)$. The embedding then places the source tape contents and head position at $j$, and the selected-tape hypotheses identify these with the corresponding data of the host configuration. If $j$ lies outside the image, the frame property for the embedding says that the embedded configuration retains the supplied ambient contents and head position; these agree with the host data by hypothesis. Thus every host tape and head position agrees. The state and input position agree by their hypotheses, and the output agrees because the prefix is empty. Extensionality of configurations now gives the claimed equality.

**Key facts.** `Turing.embedEmitCfg_selected_tape`, `Turing.embedEmitCfg_selected_pos`, `Turing.embedEmitTM_frame`.
