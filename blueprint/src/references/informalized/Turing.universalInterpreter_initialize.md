<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalInterpreter_initialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interpreter Initialization

**Claim.** When the table is the specified paired encoding of the header bits followed by $n$ ones, a run of $|T|+2|\beta|+2n+7$ steps reaches the main dispatch configuration with the stated table cursor, state tape encoding index $n$, and state cursor $1$.

**Proof.** Break the run into the initial step, a table rewind of $|T|+1$ steps, a paired-bit count of $2|\beta|+2$ steps, a unary-copy phase of $n+1$ steps, and a state rewind of $n+2$ steps. The time identity in the proof shows that these phases have exactly the claimed total length. The first step places the interpreter in the initial table-rewind phase (`universalInterpreter_first`). Rewinding the table from cursor $|T|-1$ reaches the counting phase at cursor $0$ (`universal_table_rewind`). The count-run result says that scanning the doubled header bits and the $01$ separator takes $2|\beta|+2$ steps and enters the initial-copy phase with the cursor just past that prefix (`universal_count_run`); the prefix has length $2|\beta|+2$ (`universal_pair_length`). The unary-copy phase reads the $n$ ones, writes them onto the state tape, and reaches the state-rewind phase. Finally, the state tape has its unique false marker at position $0$ (`universalStateTape_marker`), so rewinding from position $n+1$ for $n+2$ steps reaches the main dispatch state with state cursor $1$ (`universal_state_rewind`). Combining the phase endpoints gives the asserted evaluation configuration.

**Key facts.** `Turing.universalInterpreter_first`, `Turing.universal_table_rewind`, `Turing.universal_count_run`, `Turing.universal_pair_length`, `Turing.universal_unary_copy`, `Turing.universalStateTape_marker`, `Turing.universal_state_rewind`.
