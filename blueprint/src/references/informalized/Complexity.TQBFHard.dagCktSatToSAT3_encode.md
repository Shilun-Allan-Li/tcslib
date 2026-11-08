<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHard.lean :: Complexity.TQBFHard.dagCktSatToSAT3_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Encoding and 3-SAT Serialization

**Claim.** For a well-formed acyclic circuit of fan-in at most two, applying the circuit-to-3-SAT transformation to its encoding produces exactly the serialization of the CNF consisting of the output-true clause and the gates’ Tseitin clauses.

**Proof.** The decoder recognizes the encoding of a circuit as that same circuit: decoding `C.encode` returns `C` (`DAGCircuit.decode_encode`). Thus, in the definition of the transformation, the decoded-circuit branch applies. The hypothesis that the circuit has fan-in at most two makes the well-formedness and arity check true, so this branch returns `C.toCNF`. The final operation serializes that CNF, giving exactly `CNF.serialize C.toCNF`, as claimed.

**Key facts.** `BoolCircuit.DAGCircuit.decode_encode`.
