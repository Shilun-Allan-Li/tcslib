<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitCfg_ofWords_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding Word-Based Configurations

**Claim.** If the target words agree with the source words on selected tapes and with the frame words on all other tapes, embedding the configuration formed from the source words, using the frame on unselected tapes and empty output prefix, gives the configuration formed from the target words.

**Proof.** Apply `Turing.embedEmitCfg_eq` to the source and target word configurations. Their states and input-head positions agree, and both outputs are empty, so the output condition holds. On each selected tape, the target word equals the source word; applying the buffer-tape construction preserves that equality, and both head positions are zero. On each unselected tape, the frame word equals the target word, so their buffer tapes agree as well, and again both head positions are zero. These field agreements give the asserted equality.

**Key facts.** `Turing.embedEmitCfg_eq`.
