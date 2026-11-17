<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_Admin_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of an Administrative Action

**Claim.** Applying the specified administrative action changes the control state, table cursor, and state cursor as described, and either leaves the state tape unchanged or writes the specified value at its cursor.

**Proof.** The administrative action has zero input-head movement, so the input position is unchanged (the zero-movement identity, `moveInputPos_zero`). Its four work tapes are prescribed directly: the first tape receives the table movement, the second receives the state write instruction and movement, and the remaining two receive no write and zero movement. Evaluating the action’s tape updates therefore leaves the table contents and the last two tapes unchanged, while the state tape is either unchanged or updated at position $s$ according to the optional write. The head positions become $p+d_t$ and $s+d_s$ on the first two tapes; the other two positions are unchanged. The action sets the control to $q'$, performs no output, and these componentwise equalities give the claimed configuration.

**Key facts.** `Turing.moveInputPos_zero`.
