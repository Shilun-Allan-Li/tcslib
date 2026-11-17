<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean :: BoolCircuit.mem_dagCktSatLang_iff_mem_SAT3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# DAG Circuit Satisfiability and 3-SAT

**Claim.** A Boolean word belongs to the language of encodings of fan-in-two satisfiable DAG circuits exactly when the word obtained by converting its circuit-satisfiability CNF encoding to a Boolean word belongs to the language of satisfiable CNF formulas of width at most three.

**Proof.** First replace language membership by the characterization in terms of successful circuit decoding and membership in the circuit-satisfiability set (`mem_dagCktSatLang_iff_decode`). Split according to the result of decoding the word. If decoding fails, the circuit language condition is false, and the conversion assigns the unsatisfiable formula consisting of the empty clause; its serialization is not in 3-SAT (`not_mem_SAT3_serialize_nil`). If decoding succeeds with pair $C$, the decoded pair is uniquely determined. When its circuit is fan-in-two, the circuit-satisfiability membership condition is equivalent to its associated CNF being both width at most three and satisfiable (`mem_dagCktSat_iff_toCNF`). The conversion in this branch is precisely the serialization of that CNF, and decoding the serialization recovers the CNF (`CNF.decode_serialize`), so the width and satisfiability conditions are exactly the 3-SAT membership condition. When the circuit is not fan-in-two, membership in the circuit-satisfiability set is false (`mem_dagCktSat_iff`), and the conversion again yields the serialization of the empty-clause formula, which is not in 3-SAT. These cases establish both directions.

**Key facts.** `BoolCircuit.mem_dagCktSatLang_iff_decode`, `BoolCircuit.mem_dagCktSat_iff_toCNF`, `BoolCircuit.mem_dagCktSat_iff`, `BoolCircuit.not_mem_SAT3_serialize_nil`, `Std.Sat.CNF.decode_serialize`.
