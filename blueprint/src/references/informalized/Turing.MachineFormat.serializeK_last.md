<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.serializeK_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final zero in machine serialization

**Claim.** The serialization of a machine with $k$ work tapes, binary tape alphabet, and state set $\mathrm{Fin}(n+1)$ ends in a final $0$.

**Proof.** Each encoded transition action ends in $0$. Since there is at least one possible work-tape read and at least one state, the nested table enumeration is nonempty at each of its three levels. Repeatedly applying the fact that a nonempty flat-map of lists each ending in $0$ also ends in $0$ shows that the entire transition table ends in $0$. The serialization is the paired encoding of the state-count bits followed by the initial-state code and this table. Taking the preceding portion of that concatenation as the prefix proves that the serialization has the form $u\mathbin{++}[0]$.

**Key facts.** `Turing.MachineFormat.actionBitsK_last`, `Turing.MachineFormat.canonFlatMap_last`, `Turing.StepBlock.length_workReadsK`.
