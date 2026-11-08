<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeCfg_push -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Push onto a bridge stack

**Claim.** The two specified actions, first moving the head of tape $k$ left and then writing $a$ without moving, produce a configuration with state $q'$, unchanged input position and output, and stack assignment updated by prepending $a$ to the stack at $k$.

**Proof.** Only the tape indexed by $k$ is affected: the first action moves its head one cell left without writing, and the second writes the embedded symbol $a$ at that cell without moving. The index-to-stack correspondence ensures this is the tape for stack name $k$ (`bridgeKey_index`, `bridgeIndex_key`). In the bridge representation, this leftward move followed by the write places $a$ immediately before the old stack, so the represented stack becomes $a::st(k)$ (`bridgeStack_push`). Every other tape's contents and head position are unchanged. Both actions have zero input movement and emit nothing, so the input position and output are unchanged; the second action sets the control state to $q'$. Comparing the configuration fields gives the result.

**Key facts.** `Turing.bridgeKey_index`, `Turing.bridgeIndex_key`, `Turing.bridgeStack_push`.
