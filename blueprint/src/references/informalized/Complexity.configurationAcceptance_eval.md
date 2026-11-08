<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationAcceptance_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Acceptance Formula

**Claim.** Under the stated coefficient bound, evaluating the acceptance formula on the encoded bit string of a configuration gives true exactly when the configuration is halted and its output is exactly $[\mathrm{true}]$.

**Proof.** The coefficient bound ensures that the number of codec bits fits within the encoded word (`Complexity.codecBit_card_le`). Consequently, reading the encoded word at the wire corresponding to any codec bit recovers that bit's value (`Complexity.codecWord_get`). After expanding the relabeling and this encoding, the formula's evaluation is therefore the codec acceptance formula evaluated on the row encoding of the configuration. The codec acceptance formula tests that the state is the halting state and that the output summary is the accepting summary (`Complexity.codecAcceptance_eval`). By definition of the output summary, that summary is accepting exactly when the output is $[\mathrm{true}]$, proving the equivalence.

**Key facts.** `Complexity.codecBit_card_le`, `Complexity.codecWord_get`, `Complexity.codecAcceptance_eval`.
