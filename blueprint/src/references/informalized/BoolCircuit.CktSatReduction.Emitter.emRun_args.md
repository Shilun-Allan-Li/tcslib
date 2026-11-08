<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec.lean :: BoolCircuit.CktSatReduction.Emitter.emRun_args -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emission While Reading Gate Arguments

**Claim.** For a gate kind $k$ and at most two arguments, reading their encoded list from the argument-reading phase emits the serialized Tseitin formula for that gate at output index $z$, then continues in the gate phase at index $z+1$ on the remaining input.

**Proof.** Split into the three possible list lengths, which exhaust the hypothesis that there are at most two arguments. With no arguments, the list encoding immediately supplies its terminator; the machine recognizes the gate boundary, and its emitted instruction sequence agrees with the serialization of the corresponding empty-argument Tseitin formula. With one argument $j$, the unary block of true bits is read while the machine is in its first argument-collection phase. The counter-update fact for that phase ($\texttt{emRun\_u0}$) shows that the counter becomes $j$ at the separator; the following list terminator triggers gate emission. With two arguments $j,l$, the first block updates the first counter by $j$ via $\texttt{emRun\_u0}$, and the second updates the second counter by $l$ via $\texttt{emRun\_u1}$. The final separator triggers emission. In each case, the instruction program's output is exactly the clause serialization for the Tseitin formula built from the counters and output index; this is the emitter-serialization identity ($\texttt{emitBits\_eq}$). The machine then resumes in gate phase at index $z+1$ on the untouched remainder $r$.

**Key facts.** `BoolCircuit.CktSatReduction.Emitter.emRun_u0`, `BoolCircuit.CktSatReduction.Emitter.emRun_u1`, `BoolCircuit.CktSatReduction.Emitter.emitBits_eq`.
