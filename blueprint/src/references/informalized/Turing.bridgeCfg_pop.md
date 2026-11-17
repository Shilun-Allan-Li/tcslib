<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeCfg_pop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pop a nonempty bridge stack

**Claim.** When the stack at $k$ is $a::xs$, the specified action blanks its current work-tape cell and moves its head right, producing the bridge configuration with that stack replaced by $xs$, while leaving the input position and output unchanged.

**Proof.** The action has zero input movement, which fixes the input-head position (`moveInputPos_zero`). It writes blank at the selected tape's current cell and moves that tape's head one cell right; all other tapes receive no write and no movement. The four stack names and tape indices correspond (`bridgeKey_index`, `bridgeIndex_key`), so this action affects exactly the tape for $k$. In the stack representation, the current cell of the nonempty stack contains its head symbol; blanking it and shifting the head right exposes the tail (`bridgeStack_pop`). The successor state is $q'$, and no output symbol is emitted. These fieldwise changes give the claimed bridge configuration.

**Key facts.** `Turing.moveInputPos_zero`, `Turing.bridgeKey_index`, `Turing.bridgeIndex_key`, `Turing.bridgeStack_pop`.
