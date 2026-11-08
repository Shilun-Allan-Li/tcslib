<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean :: BoolCircuit.not_mem_SAT3_serialize_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The empty-clause encoding is not in 3SAT

**Claim.** The encoding of the CNF formula consisting of a single empty clause does not belong to the language of bit strings whose decoded formulas have width at most three and are satisfiable.

**Proof.** Suppose the encoding belonged to the language. Then its decoded formula would be satisfiable, so some Boolean assignment would make that formula evaluate to true. Encoding followed by decoding recovers the original formula (`Std.Sat.CNF.decode_serialize`), so this would give an assignment satisfying the formula with one empty clause. An empty clause is false under every assignment, and therefore a conjunction containing it cannot be true. This is a contradiction.

**Key facts.** `Std.Sat.CNF.decode_serialize`.
