<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.DAGCircuit.satisfiable_iff_toCNF_satisfiable_of_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfiability for Fan-In-Two Circuits

**Claim.** For a circuit satisfying the fan-in-two conditions, circuit satisfiability is equivalent to satisfiability of its associated CNF formula.

**Proof.** The fan-in-two hypothesis includes the bound that every gate has at most two inputs. Applying the circuit-to-CNF satisfiability equivalence under that bound gives the result directly.

**Key facts.** `BoolCircuit.DAGCircuit.satisfiable_iff_toCNF_satisfiable`.
