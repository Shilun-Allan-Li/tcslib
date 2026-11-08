<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arCfg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol Under Encoding

**Claim.** For a binary input and a configuration on its letterwise image under the embedding, the scanned symbol in the encoded configuration, mapped through the embedding, equals the symbol scanned in the original configuration.

**Proof.** The encoding preserves the input-head position and replaces the input list by its letterwise image. If the head is at either boundary position, both configurations scan no symbol. Otherwise, both select the same list index; the encoded list contains the embedded version of the original symbol there, so mapping that symbol through the embedding gives the original scanned symbol.
