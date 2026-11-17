<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_skip_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Skip Across a Delimited Block

**Claim.** Starting at the prefix cursor before $n$ ones followed by a zero, unary skipping takes $n+1$ steps, advances the table cursor past the delimiter, and either enters the destination continuation when the counter is zero or begins fixed-field skipping with the counter decreased by one.

**Proof.** Induct on $n$, generalizing the prefix. When $n=0$, the next table cell is the delimiter $0$: the table-reading fact (`Turing.timedCut_table_read`) identifies the symbol, and the interpreter's one-step transition (`Turing.timedCut_Eval_step`) moves right and selects the stated continuation according to whether the counter is zero. The zero-step and one-step run laws (`Turing.MultiTapeTM.runFrom_zero` and `Turing.MultiTapeTM.runFrom_succ_eq_step`) give the claimed run. For the successor case, the next cell is $1$, again by the table-reading fact. The one-step transition keeps the unary-skip control and advances both the table cursor and state-tape cursor as prescribed; here the state tape is unchanged because no write is requested. The remaining table has the same form with prefix extended by this $1$ and with $n$ ones left. Apply the induction hypothesis to that suffix. Composing this first step with the remaining run yields $n+2$ steps in total and places the table cursor just past all the ones and the delimiter.

**Key facts.** `Turing.timedCut_table_read`, `Turing.timedCut_Eval_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
