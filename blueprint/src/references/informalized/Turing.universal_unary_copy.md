<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_unary_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Cost Unary State Copy

**Claim.** When the table field consists of $n$ ones followed by zero, the prescribed transitions copy those $n$ unary marks onto the state tape. After $n+1$ steps the control is $q'$, the table cursor is $|l|+n+d$, and the state tape is the unary state-$j+n$ tape with cursor $j+n+1$.

**Proof.** Induct on $n$, allowing both the table prefix $l$ and unary state index $j$ to vary. For $n=0$, the current table cell is zero by `universal_table_read`; the assumed zero-transition rule enters $q'$, moves the table cursor by $d$, and leaves the state tape and its cursor unchanged. One-step evaluation (`universalEval_step`) and the zero-step run identity (`runFrom_zero`) give the base case. For the successor case, the current cell is one by the same table-reading fact. The one-transition rule writes one at the current state cursor, moves both cursors right, and remains in $q$. The state-tape update identity (`universalStateTape_append`) identifies the updated tape as the unary state-$(j+1)$ tape. Treat the consumed table one as part of the prefix, leaving $n$ ones and the terminating zero. The induction hypothesis, now at state index $j+1$, handles the remaining field and enters $q'$ at the claimed final positions. Combining the first transition with that remaining run gives exactly $n+2$ steps, the required count for $n+1$ ones.

**Key facts.** `Turing.universal_table_read`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.universalEval_step`, `Turing.universalStateTape_append`.
