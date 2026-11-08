<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeCfg_pop_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pop a bridge stack and emit a symbol

**Claim.** If the stack at $k$ is $a::xs$, the action that blanks its current cell, moves the head right, and emits optional symbol $e$ yields the bridge configuration with stack $xs$ and output extended by $e$, leaving the input position unchanged and setting the state to $q'$.

**Proof.** First use the nonempty-stack pop result (`bridgeCfg_pop`), which identifies the resulting state, tape contents, and head positions. The action with output $e$ has the same state, input movement, and work-tape operations; its only additional effect is to append the list represented by $e$ to the existing output. Since applying an action appends its emitted symbol to the output, the final output is $out ++ e.toList$. The input movement is zero, so the input-head position remains $p$ (`moveInputPos_zero`). These fieldwise equalities establish the asserted configuration.

**Key facts.** `Turing.bridgeCfg_pop`, `Turing.moveInputPos_zero`.
