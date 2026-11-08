<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_body_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration of the Controller

**Claim.** For every input word, the combined controller's initial configuration is the anchor seam configuration with all work tapes blank.

**Proof.** The initial-configuration identity for a machine states that its initial configuration is its initial state on the given input with every work tape blank. The combined controller has initial state the anchor. A word configuration with the empty word assigned to every tape has the same state, head positions, blank tape contents, and empty output as this initial configuration. Hence the two configurations agree.

**Key facts.** `Turing.initCfg_ofWords`.
