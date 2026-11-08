<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine.lean :: BoolCircuit.CircuitEval.macro_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded simulation of an abstract update

**Claim.** From an invariant state, one abstract update either produces an invariant successor with at most one additional computed value, reached by the evaluator within $2|s.\mathrm{vals}|+4$ steps, or produces a Boolean value and the machine halts with that output within the same bound.

**Proof.** Write the abstract state as $(\phi,\mathrm{vals},\mathrm{ms},j)$. Apply the two-step transition theorem (`lstep`) to reach the configuration after processing the current input pair. The buffer-tape and mark-tape lookup identities identify the scanned symbols with the abstract values at position $j$. The local-action validity theorem (`lact_ok`) now supplies the relevant restrictions on the resulting action. Split on its next state.

If the action halts, its validity guarantees an emitted bit. The machine has then halted after the two transition steps, and its output is that bit. This is within the stated bound.

If the next state is a read phase, the action-validity conditions show that no value was written, any new mark is placed at an index whose value is present, and the movement either leaves $j$ unchanged or advances it to $j+1$. The invariant bounds on $j$ and the marks therefore persist; the main-phase condition is supplied by `lact_ok`, and its walking-phase condition preserves the zero-head requirement. The configuration after the two steps encodes the resulting abstract state, whose value list is unchanged.

If the next state is a value-tape rewind, validity gives a present value at $j$, a leftward move, and a nonwalking main destination. Hence $j<|\mathrm{vals}|$. The mark, if added, is consequently still within the value list. The rewind theorem (`rew`) returns the relevant tape head to zero in $j+1$ further steps, yielding the configuration encoding the successor state; this state satisfies the invariant and its value list is unchanged.

Finally, if the action enters an append state, validity says the current phase is not walking, so the invariant forces $j=0$. The append simulation (`app_walk`) appends the output bit to the value list and clears the marks, then the rewind theorem (`rew`) returns the value head to zero and enters the next main phase. The invariant follows, and the value list has grown by exactly one. In these cases, the two initial steps plus the rewind or append-and-rewind duration are bounded by $2|\mathrm{vals}|+4$. The run-composition law (`Turing.MultiTapeTM.runFrom_add`) concatenates these segments and gives the stated configuration equality.

**Key facts.** `BoolCircuit.CircuitEval.lstep`, `Turing.FinTM.bufferTape_nat`, `BoolCircuit.CircuitEval.tapeM_nat`, `BoolCircuit.CircuitEval.lact_ok`, `BoolCircuit.CircuitEval.rew`, `BoolCircuit.CircuitEval.app_walk`, `BoolCircuit.CircuitEval.wr_tapeM`, `Turing.MultiTapeTM.runFrom_add`.
