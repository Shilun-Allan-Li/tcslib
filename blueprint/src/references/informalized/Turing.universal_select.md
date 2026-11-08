<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universal_select -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Cost Record Selection

**Claim.** Under the stated encoding hypotheses, starting in the record-group phase with index $i$ reaches the action-reading phase at field $0$ after exactly $2g+|G|+|B|+3$ steps, with the specified table cursor, cleared bit register, and zero unary state counter.

**Proof.** Write $P$ for the concatenation of the records in the groups and $Q$ for the records in the list of actions preceding index $i$. First, the group-skipping result says that after $g+|P|+1$ steps, the interpreter has passed all groups and reached the state-rewind phase. The state tape is now the unary encoding of zero, with its marker at position $0$; the state-tape marker property (`Turing.universalStateTape_marker`) ensures the rewind scans to that marker. The state-rewind result (`Turing.universal_state_rewind`) then takes $g+2$ steps to put the state cursor back at $1$ and enter the appropriate continuation. If $i=0$, there are no preceding records and this continuation is already the action-reading phase. If $i>0$, the list-skipping result says that skipping the $|Q|$ bits of those records reaches that same phase, with the table cursor advanced by $|Q|$. The total cost is $(g+|P|+1)+(g+2)+|Q|=2g+|P|+|Q|+3$. The run-addition law (`Turing.MultiTapeTM.runFrom_add`) composes these successive runs; the table decomposition and the stated window identities identify the resulting configuration and cursor values.

**Key facts.** `Turing.universal_skip_groups`, `Turing.universalStateTape_marker`, `Turing.universal_state_rewind`, `Turing.universal_skip_records`, `Turing.MultiTapeTM.runFrom_add`.
