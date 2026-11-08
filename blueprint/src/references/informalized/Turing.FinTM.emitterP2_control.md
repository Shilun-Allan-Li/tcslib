<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_control -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Silent Seam Dispatch

**Claim.** A transition that keeps every head stationary, writes nothing, emits nothing, and changes state from $q$ to $r$ takes the seam configuration on the same tape words to the seam configuration in state $r$.

**Proof.** The transition hypothesis makes the selected action the control action with zero input-head movement and successor state $r$. Applying this action changes only the state and input-head position; all work tapes and work-head positions remain as they were, and no output is appended (`Turing.FinTM.controlAction_apply`). Zero movement leaves the input-head position unchanged (`Turing.moveInputPos_zero`). Thus the result has precisely the same tape words and seam positions, with state $r$.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
