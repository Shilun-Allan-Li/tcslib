<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.lenParse_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Step of the Pair Parser

**Claim.** If $x=pbs$, then one step from the length checker’s parse configuration at position $|p|$ records $b$ in the parser state, moves the input head to position $|p|+1$, and leaves the counter unchanged.

**Proof.** The parse-state transition reads the current input symbol and, when it is present, records that bit and moves right. Since $x=pbs$, the symbol at index $|p|$ is $b$; the configuration’s input-symbol rule identifies exactly this symbol (`lenCfg_read`). The rightward move reaches position $|p|+1$ because this position is not the right boundary (`moveInputPos_pos_of_ne_right`). Applying the transition changes only the parser state and input-head position: the counter is unchanged, and there is no output. This configuration update is the content of `lenAction_apply`.

**Key facts.** `Turing.FinTM.lenCfg_read`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.lenAction_apply`.
