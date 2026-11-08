<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.timed_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Decider's Output

**Claim.** If the decider is halted with output $[b]$, then two controller steps from its decider-phase configuration reach the ready configuration for bit $b$.

**Proof.** Let the ready configuration be the one specified in the claim. Since the decider is halted, the controller is in its post-capture control state. Its first step changes to the next control state and rewinds the extra tape head; the other tape contents and head positions are unchanged. The resulting configuration is the ready configuration with its state replaced by the intermediate reading state. On the next step the controller reads the extra tape, whose head points to the stored bit $b$. It therefore records $b$ in its control state and leaves the tapes, heads, input position, and output unchanged. The control action changes only the state and leaves the input head fixed (`controlAction_apply`, with the fact that a zero input movement preserves position, `moveInputPos_zero`). This gives the ready configuration.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
