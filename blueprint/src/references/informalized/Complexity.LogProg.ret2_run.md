<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean :: Complexity.LogProg.ret2_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Rewind After a Return

**Claim.** Starting in the second return phase at input-head position $j\le |x|$, the machine keeps all work-head positions fixed through time $j+1$ and then reaches input-head position $1$ in the return successor determined by the call and register index zero, with tapes, positions, and output unchanged.

**Proof.** Induct on $j$. At $j=0$, the input head is at the left boundary, so it reads no input symbol. The second return phase therefore moves it right and enters the successor determined by `nextRet`; this is the claimed configuration after one step. Before that step, at time zero, all work-head positions are unchanged.

For the successor step, the current position is $j+1$, so the input head reads $x[j]$. The transition in the second return phase moves left, leaves every work tape and work-head position unchanged, and stays in that phase. The negative-move position formula (`Turing.FinTM.moveInputPos_neg_val`) shows that the new input-head value is $j$. Apply the induction hypothesis from this new configuration. The step decomposition for runs (`Turing.MultiTapeTM.runFrom_succ_eq_step`) then transfers its endpoint and all intermediate work-position equalities to the original run, including time zero.

**Key facts.** `Complexity.LogProg.mkCfg_state`, `Complexity.LogProg.apply_inputOnly`, `Turing.FinTM.moveInputPos_neg_val`, `Turing.inputSymbolInner`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
