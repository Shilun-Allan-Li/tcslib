<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean :: Complexity.LogProg.regBack_x -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register head returns to the origin

**Claim.** Under the stated transition rule, a head starting at position $q$ moves left over the symbols of register $r$ and then moves right once onto blank, entering $n_x$ at position $0$. The endpoint and all intermediate configurations satisfy the stated head-position bounds.

**Proof.** Induct on the number $n$ of steps, with $q+1=n$. If $n=0$, then $q=-1$; the scanned cell is blank, so the transition enters $n_x$ and moves the head right to $0$. The only earlier time is the initial configuration, whose head position is $-1$. For the successor case, write $q=j$ with $j$ a natural number. Since $j<|w|$, the scanned cell contains the $j$th symbol of $w$. The transition therefore moves the head left by one and remains in state $s_0$. Apply the induction hypothesis from the new position $q-1$, with one fewer step; its endpoint reaches $n_x$ at $0$. The one-step run calculation (`rrun_one_x`, `apply_xAct`, `xCfg_read`) identifies this first move and confirms that the input head, tape contents, output, and other register heads are unchanged. Concatenating the first move with the inductive run gives the endpoint. Any earlier time is either time $0$, with head at $q$, or occurs during the remaining run; in the latter case the induction hypothesis bounds the head between $-1$ and $q-1$, hence also between $-1$ and $q$. The run-addition law (`rrun_add`) justifies this split.

**Key facts.** `Complexity.LogProg.rrun_one_x`, `Complexity.LogProg.xCfg_read`, `Complexity.LogProg.apply_xAct`, `Complexity.LogProg.rrun_succ_left`, `Complexity.LogProg.rrun_add`.
