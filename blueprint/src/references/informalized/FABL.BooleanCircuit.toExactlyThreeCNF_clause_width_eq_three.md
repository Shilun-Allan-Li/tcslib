<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.toExactlyThreeCNF_clause_width_eq_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact width of encoded clauses

**Claim.** Every clause in the exactly-three-CNF encoding of a circuit has width exactly $3$.

**Proof.** The circuit's width-three CNF encoding has width at most $3$ (`toWidthThreeCNF_width_le`). The general exact-three-CNF construction turns any CNF formula of width at most $3$ into one whose clauses all have width exactly $3$ (`exactlyThreeCNF_clause_width_eq_three`). Applying that result to the circuit's width-three encoding gives the stated width for each clause in the resulting formula.

**Key facts.** `FABL.BooleanCircuit.toWidthThreeCNF_width_le`, `FABL.exactlyThreeCNF_clause_width_eq_three`.

**Caveat.** The supplied theorem establishes exact clause width; it does not establish the informal statement's size bound.
