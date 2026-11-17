<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRecord_prepare_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepared recorder configuration

**Claim.** Replacing the loader's control with the recorder's initial state gives exactly the recorder configuration at time zero, initialized on virtual input $y$, with zero movement counters, an empty record, parameter $T$, and the retained words in their designated tapes.

**Proof.** The prepared recorder's initial frame has a canonical word-based description: the recorder's own tapes contain empty words, the clock tape contains $T$ true symbols, the virtual input tape contains $y$, and the source-machine tapes are empty. The preparation identity (`Complexity.clRec_prepared`) identifies that word-based frame with the recorder configuration at time zero, whose source machine is initialized on $y$, whose counters are zero, and whose record is empty. Replacing the loader control by the recorder's initial control changes only the state field. The tape placements in the loader frame and recorder frame agree slot by slot: recorder tapes match the canonical frame, the four retained slots contain `keep`, and the input buffer contains $x$. Equality of the state and input-position fields together with these tape-by-tape identities proves equality of the full configurations.

**Key facts.** `Complexity.clRec_prepared`.
