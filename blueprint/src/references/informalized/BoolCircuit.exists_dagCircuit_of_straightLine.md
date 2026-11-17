<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.exists_dagCircuit_of_straightLine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit representation of a straight-line program

**Claim.** A straight-line program on $n$ Boolean inputs of length at most $S$ that computes a Boolean function can be represented by a well-formed acyclic circuit with fan-in at most two computing that function and of size at most $2n+\max(S,1)$.

**Proof.** Choose a straight-line program $P$ of length at most $S$ that computes the function. Convert it to its associated circuit. This circuit is well-formed and has fan-in at most two (`BoolCircuit.StraightLineProgram.toCircuit_isFaninTwo`), and its evaluation agrees with that of $P$ on every input (`BoolCircuit.StraightLineProgram.toCircuit_eval`). Hence it computes the desired function. The conversion gives size exactly $2n+\max(\mathrm{length}(P),1)$ (`BoolCircuit.StraightLineProgram.toCircuit_size`), which is at most $2n+\max(S,1)$ because $\mathrm{length}(P)\le S$.

**Key facts.** `BoolCircuit.StraightLineProgram.toCircuit_isFaninTwo`, `BoolCircuit.StraightLineProgram.toCircuit_eval`, `BoolCircuit.StraightLineProgram.toCircuit_size`.
