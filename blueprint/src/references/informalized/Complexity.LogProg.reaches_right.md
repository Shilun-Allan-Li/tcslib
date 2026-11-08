<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.reaches_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step rightward head movement

**Claim.** Under the stated transition hypotheses, a configuration with state $s$, input-head position $q$, and register head $r$ at $p$ reaches in one step the same configuration data with state $s'$ and input-head position $q+1$.

**Proof.** The one-step run formula for a non-call state (`Complexity.LogProg.rrun_one_x`) expresses the next configuration as the ordinary machine transition applied to the initial configuration. The transition hypothesis says that, for the symbols currently read, this action is the specified one: it moves the input head right, leaves the work tapes and their head positions unchanged, emits no output, and enters $s'$. Applying the action therefore preserves all the other configuration data; the action-on-configuration identity (`Complexity.LogProg.apply_xAct`) makes this preservation explicit. Finally, because $q\le |x|$, the input-head position update has value $q+1$ (`Complexity.LogProg.moveInputPos_pos_val`), yielding the claimed configuration.

**Key facts.** `Complexity.LogProg.rrun_one_x`, `Complexity.LogProg.apply_xAct`, `Complexity.LogProg.moveInputPos_pos_val`.
