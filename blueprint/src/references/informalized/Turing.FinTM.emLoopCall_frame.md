<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emLoopCall_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forwarding Call Decomposition

**Claim.** The forwarding call equals the capturing call formed from the configuration with empty output, with physical output set to the chosen prefix followed by the original output.

**Proof.** Compare the two configurations field by field. Their states agree because both use the same embedding and return state, and their input-head positions agree by construction. On each work tape, the cases for tapes belonging to the original configuration agree directly; on the added tape, the capture construction uses the prefix followed by the emptyed configuration's output, which is precisely the prefix followed by the original output. The head positions agree by the same division into original and added tapes. Finally, the forwarding construction's output is the prefix followed by the original output, as specified on the right. Hence all configuration fields coincide.
