<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.erase_run_outside -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasure preserves behavior outside the reach set

**Claim.** If an input pair does not reach the subprotocol being erased, then the erased protocol and the original protocol produce the same output on that pair.

**Proof.** Choose a path witnessing that the subprotocol is contained in the protocol. By the path-level erasure result (`erasePath_run_outside`), any input pair outside the path's reach set gives the same output when run on the erased path and on the original protocol. Unfolding the definitions of erasure, reach, and reaching identifies these path-level objects with the stated protocol-level ones, yielding the equality.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.erasePath_run_outside`.
