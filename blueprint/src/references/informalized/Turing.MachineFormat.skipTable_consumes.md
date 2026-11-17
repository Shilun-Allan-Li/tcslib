<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.skipTable_consumes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Skip table length bound

**Claim.** If the table skipper with parameters $k,n$ accepts $xs$ and returns $ys$, then $(4k+5)3^{k+1}(n+1)+|ys|\le |xs|$.

**Proof.** First consider one successful action skip. The erasure identity (`codeEraseActionK`) lets us view it as reading an encoded action and returning the remaining suffix. Soundness of that read (`codeReadActionK_sound`) identifies the input as the action’s encoding followed by that suffix. The action encoding has length at least $4k+5$ (`codeActionK_length`), so each successful action skip consumes at least $4k+5$ symbols. Applying the iterated triple-skip bound (`skipSymbols_consumes`) to the $k+1$ levels of triple repetition shows that one such repeated reader consumes at least $(4k+5)3^{k+1}$ symbols. Finally, the table skipper repeats that reader $n+1$ times. The repeated-reader consumption bound (`skipRepeat_consumes`) multiplies the per-iteration bound by $n+1$ and adds the final suffix length, yielding the claimed inequality.

**Key facts.** `Turing.codeEraseActionK`, `Turing.codeReadActionK_sound`, `Turing.codeActionK_length`, `Turing.MachineFormat.skipSymbols_consumes`, `Turing.MachineFormat.skipRepeat_consumes`.
