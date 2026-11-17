<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_unary_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying a Unary Table Field

**Claim.** When the table contains $n$ ones followed by a zero, the stated transitions copy those ones onto the unary state tape and then take the zero transition. After $n+1$ steps the table cursor is at $|l|+n+m$, the tape encodes $j+n$, and its head is at $j+n+1$.

**Proof.** Induct on $n$, generalizing the prefix and the encoded value $j$. If $n=0$, the next table symbol is the delimiter $0$, as given by the table-reading fact (`Turing.timedCut_table_read`). The assumed zero-transition rule and the one-step evaluation result (`Turing.timedCut_Eval_step`) move to $q'$, move the table head by $m$, and leave the state tape and its head fixed. The zero-step and successor run laws (`Turing.MultiTapeTM.runFrom_zero` and `Turing.MultiTapeTM.runFrom_succ_eq_step`) give the result. If $n+1$ ones remain, the next symbol is $1$. The assumed one-transition rule and `Turing.timedCut_Eval_step` advance both heads by one and write a $1$ at the current state-tape position. The state-tape update fact (`Turing.timedCut_StateTape_append`) says this extends the unary encoding of $j$ to that of $j+1$. The remaining table has a prefix extended by one $1$, and the induction hypothesis applies with encoded value $j+1$. Combining its run with the first step yields the claimed head positions, encoding, and total of $n+2$ steps.

**Key facts.** `Turing.timedCut_table_read`, `Turing.timedCut_Eval_step`, `Turing.timedCut_StateTape_append`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
