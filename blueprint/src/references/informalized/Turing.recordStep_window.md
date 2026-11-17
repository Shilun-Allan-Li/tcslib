<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_window -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of the Tape Window

**Claim.** After applying an action to a configuration contained in the window $[-s,s]$, the resulting configuration remains in that window exactly when no head at the left endpoint moves left and no head at the right endpoint moves right.

**Proof.** Fix a tape. Its new head position is its old position plus the action’s movement, which is one of $-1,0,1$. Since the old position lies in $[-s,s]$, checking these three possible movements shows that the new position lies in the interval exactly when the head is not at $-s$ while moving left and not at $s$ while moving right. This proves the equivalence for all head positions. For tape contents, consider any position outside the window. It differs from the old head position, since that head lies inside the window. If the action does not write, the tape content there is unchanged; if it writes, only the old head position is updated. In either case it remains blank by the original outside-window hypothesis. Thus the only additional condition for preserving the window is the stated endpoint condition on every tape.
