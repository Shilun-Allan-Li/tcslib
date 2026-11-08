<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.DAGGate.length_tseitin_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Tseitin Clause Count

**Claim.** The Tseitin CNF encoding of any gate has at most four clauses.

**Proof.** Write the gate as a kind and an argument list, and split by the number of inputs. For zero inputs the encoding has one clause, for one input it has two, and for two inputs it has four. With three or more inputs the encoding is empty. Each case has at most four clauses.
