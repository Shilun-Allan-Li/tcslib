<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clMatch_stop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exhausted Clock Stops the Matcher

**Claim.** When the matcher is in its initial search control with clock position $N$, one step takes it to completed control and leaves its tapes and work-head positions unchanged.

**Proof.** At clock position $N$, the clock tape is the word of $N$ true symbols with its head at position $N$. The symbol scanned there is blank, since the word ends at that position. The initial search branch therefore chooses the zero-movement control action leading to completed control. The action changes only the state and input-head position; its input movement is zero, so the input-head position is also unchanged. The stated control-action behavior (`Turing.FinTM.controlAction_apply`) and the fact that zero movement fixes the input-head position (`Turing.moveInputPos_zero`) show that the resulting configuration differs only in its control state.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
