<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec.lean :: BoolCircuit.CktSatReduction.Emitter.emitBits_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Emitted bits encode gate clauses

**Claim.** For each gate kind, arity code, and counter vector, the bits emitted by the gate program are exactly the body serialization of its Tseitin CNF with output variable $v(0)$ and arguments selected from $v(1),v(2)$.

**Proof.** Expand the emitted bits as the execution of the program generated from the Tseitin formula. The program-to-serialization lemma says that executing any generated CNF program produces the body serialization after replacing each literal variable $x$ by the tape value indexed by $x\bmod 3$, preserving its polarity. Apply this with output variable zero and arguments prescribed by the arity code. In each of the three gate-kind cases and three arity cases, the selected indices reduce to the corresponding components of $v$, so the resulting body is exactly the stated serialization.

**Key facts.** `BoolCircuit.CktSatReduction.Emitter.flatMap_exec_progOf`.
