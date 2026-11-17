<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean :: Complexity.LogProg.apply_inputOnly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Only Action

**Claim.** An action that moves only the input head, emits no output, and enters state $st'$ changes the state and input-head position as specified while leaving both work-tape banks, all head positions, and the output unchanged.

**Proof.** Compare the configuration fields. The action directly sets the state to $st'$, and its input-head component applies the clamped movement $mv_I$. Every work-tape instruction is absent with zero movement, so each tape and each work-head position is unchanged, whether the index lies in the register bank or the decider bank. Since the action emits no symbol, the output is unchanged as well.
