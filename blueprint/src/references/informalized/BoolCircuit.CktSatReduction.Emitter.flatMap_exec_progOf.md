<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec.lean :: BoolCircuit.CktSatReduction.Emitter.flatMap_exec_progOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the generated program

**Claim.** Executing the program generated from a CNF under a three-component counter vector produces the body encoding of the formula obtained by replacing each literal variable $x$ with the value at index $x\bmod 3$, preserving its polarity.

**Proof.** First prove the corresponding statement for one clause by induction on its literals. For the empty clause both sides are empty. For a literal $(x,b)$, its program prints $v(x\bmod 3)$ true bits, then outputs true, false, and the polarity bit $b$. These are precisely the serialization of the replaced literal, followed by the clause's remaining literal serializations. Now induct on the list of clauses. Each clause contributes an initial true bit, its literal serializations, and the terminating false bit. The clause induction identifies the literal portion, and the definitions of clause serialization and body encoding assemble these contributions across the formula.
