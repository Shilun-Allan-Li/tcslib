<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionSpec.lean :: BoolCircuit.CktSatReduction.Emitter.gateClauses_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate clauses encode circuit CNF

**Claim.** For a circuit whose gates have at most two arguments, running the gate-clause encoder on its encoding yields exactly the serialization of the concatenated Tseitin clauses, starting at variable index $n$.

**Proof.** Expand the circuit encoding into the unary encoding of $n$, the encoded gate list, and the encoded output. The emitter's initial phase consumes the $n$ unary bits, advancing its vertex counter from zero to $n$ while leaving the remaining input to be processed. The gate-phase lemma then says that processing the encoded gates from counter $n$ emits the body serialization of their concatenated Tseitin clauses, followed by the final false bit. The hypothesis that every gate has at most two arguments is exactly the condition needed for this gate-phase lemma. Finally, serialization of the whole CNF is its body serialization with that same terminating false bit, giving the result.

**Key facts.** `BoolCircuit.CktSatReduction.Emitter.emRun_n`, `BoolCircuit.CktSatReduction.Emitter.emRun_gates`, `BoolCircuit.CktSatReduction.Emitter.serialize_eq_serBody`.
