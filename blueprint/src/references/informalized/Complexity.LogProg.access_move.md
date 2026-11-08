<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_move -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Head Movement

**Claim.** Applying the action that leaves the input head fixed, moves work tape $2$ by $mv$, and enters state $st'$ changes the tape-$2$ head position from $q$ to $q+mv$ and preserves the other data.

**Proof.** The action-on-configuration identity for a work-tape move (`Complexity.LogProg.apply_xAct`) says that this action enters $st'$, moves the selected work-tape head from $q$ to $q+mv$, and moves the input head by the specified input movement. Here that movement is zero, so the input-head position is unchanged (`Turing.moveInputPos_zero`). The tape contents, other heads, and output are unchanged; the resulting configuration is precisely the one asserted.

**Key facts.** `Complexity.LogProg.apply_xAct`, `Turing.moveInputPos_zero`.
