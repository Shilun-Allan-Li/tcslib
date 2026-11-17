<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_timed_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Selected Branch

**Claim.** If $c$ is halted with output $[b]$, then two steps from its control configuration put the timed conditional machine in the ready configuration for branch $b$, retaining $c$'s input-head position and original work tapes and heads.

**Proof.** Write $R$ for the ready configuration specified in the claim. Since $c$ is halted, its control configuration is in the waiting state. The first transition moves to the scanning state; it leaves the input head in place and preserves the original work-tape block. It also moves the extra tape head back over the stored output symbol, so the resulting configuration is $R$ with its state replaced by the scanning state. The second transition reads the extra tape's symbol. That symbol is $b$, because the extra tape stores the one-symbol output $[b]$ at the head position. The transition records $b$ in the ready state and leaves the other configuration data unchanged. The identity action behavior used here is the control-action application formula (`controlAction_apply`), together with the fact that zero movement leaves the input head fixed (`moveInputPos_zero`).

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
