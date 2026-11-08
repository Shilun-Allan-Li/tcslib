<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCopy_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absorbing Completed Copier State

**Claim.** For every Boolean input word and every copier configuration whose control is the completed state, one copier step leaves the entire configuration unchanged.

**Proof.** In the completed state the copier's transition is the control action that keeps the same state and requests zero movement on the input head and every work head, with no writes or output. A zero input-head move fixes the input-head position (`Turing.moveInputPos_zero`). Since there are no work-tape writes and no head movements, the work tapes and work-head positions remain unchanged; the output is unchanged as well. Thus the whole configuration is fixed.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
