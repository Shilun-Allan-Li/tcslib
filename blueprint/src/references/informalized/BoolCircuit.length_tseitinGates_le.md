<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.length_tseitinGates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause count for successive gate encodings

**Claim.** Encoding a finite list of gates successively, starting at vertex index $z$, produces at most four clauses per gate.

**Proof.** Induct on the gate list, with the starting index arbitrary. The empty list produces no clauses. For a list with first gate $g$ and tail $gs$, the encoding is the concatenation of the encoding of $g$ and the successive encoding of $gs$, starting at $z+1$. A single gate contributes at most four clauses (`BoolCircuit.DAGGate.length_tseitin_le`), and the induction hypothesis bounds the tail by four times its length. Adding these bounds gives at most $4+4|gs|=4(1+|gs|)$ clauses.

**Key facts.** `BoolCircuit.DAGGate.length_tseitin_le`.
