<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitPoly_loop_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary generator loop termination

**Claim.** Starting the unary polynomial generator in its loop state with empty input, zero work-head positions, unary work tapes of length $q>0$, and empty output, after $T_{c+1}(q,C)+1$ steps it is halted with the tapes and head positions restored and with $Cq^{c+1}$ ones in the output.

**Proof.** Apply the loop calculation `catalogPoly_loop` at level $i=c$, with the current head index $j=0$ and remaining count $r=q$. Its hypotheses hold because the initial head position is $0$; the tape contents are the unary word of length $q$, and $j+r=q$. The calculation shows that after $q(T_c(q,C)+2)+q+2=T_{c+1}(q,C)$ steps the machine is in the advance state for level $c+1$, with all work-head positions restored to zero and output length $q(Cq^c)$. The output is a string of ones, and $q(Cq^c)=Cq^{c+1}$ by the successor law for powers. One more transition in this terminal advance state halts without moving heads, changing tapes, or appending output. The run-after-one-step identity (`runFrom_succ_eq_step'`) therefore gives the stated halted configuration.

**Key facts.** `Turing.FinTM.catalogPoly_loop`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
