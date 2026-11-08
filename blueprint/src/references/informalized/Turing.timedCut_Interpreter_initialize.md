<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_Interpreter_initialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Interpreter Initialization

**Claim.** For a table encoding the specified bit word and unary record prefix, the interpreter reaches the stated main-phase evaluation configuration after exactly $|T|+2|b|+2n+7$ steps.

**Proof.** Write the encoded prefix as the doubled-bit block followed by the two-symbol delimiter; its length is $2|b|+2$ (`Turing.universal_pair_length`). Split the run into the initial step, the table rewind, the doubled-bit count, the unary copy, and the state rewind. The run-addition law allows these successive run lengths to be composed (`Turing.MultiTapeTM.runFrom_add`). The first step enters the initial rewind-table phase with the state tape encoding $0$ (`Turing.timedCut_Interpreter_first`). Rewinding across the table takes $|T|+1$ steps and reaches the count phase at cursor zero (`Turing.timedCut_table_rewind`). The count phase scans the doubled-bit block and delimiter in $2|b|+2$ steps, reaching the initial-copy phase at the end of that prefix (`Turing.timedCut_count_run`). The unary-copy phase copies the $n$ ones, taking $n+1$ steps and leaving the state tape encoding $n$ (`Turing.timedCut_unary_copy`); the block-length identity identifies its cursor with $2|b|+2+n+1$. Finally, the state-rewind phase takes $n+2$ steps and reaches the main phase with state cursor $1$ (`Turing.timedCut_state_rewind`). The marker property of the unary state tape supplies the stopping cell at zero and ensures no positive cell is mistaken for that marker (`Turing.universalStateTape_marker`). Adding the five lengths gives $1+(|T|+1)+(2|b|+2)+(n+1)+(n+2)=|T|+2|b|+2n+7$, as required.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.timedCut_Interpreter_first`, `Turing.timedCut_table_rewind`, `Turing.timedCut_count_run`, `Turing.universal_pair_length`, `Turing.timedCut_unary_copy`, `Turing.timedCut_state_rewind`, `Turing.universalStateTape_marker`.
