<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.embedCfg_workTapeSymbols -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Selected Tape Symbols

**Claim.** For each of the first $m$ tapes, changing the embedded configuration’s state to any $b\in B$ leaves its symbol under the head equal to the symbol under the corresponding head in the original configuration.

**Proof.** Fix a tape index $i<m$. Its image under the inclusion into the $k$ tape indices is still less than $m$, so the embedding assigns that tape the original tape contents and head position. Evaluating the contents at that head therefore gives the original symbol under the head. Updating the state does not affect either tape field, proving the equality for every $i$.
