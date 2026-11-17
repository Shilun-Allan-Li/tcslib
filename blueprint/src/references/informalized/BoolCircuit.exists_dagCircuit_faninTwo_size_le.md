<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.exists_dagCircuit_faninTwo_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-in-two circuit size bound

**Claim.** For every Boolean function on $n$ variables, there is a well-formed acyclic circuit computing it, with at most two inputs per gate and size at most $n2^n+2n+1$.

**Proof.** Use the circuit obtained from the disjunctive normal form of the function. The DNF circuit computes the function (`BoolCircuit.dnfDAG_eval`), is well-formed with fan-in at most two (`BoolCircuit.dnfDAG_isFaninTwo`), and has size at most $n2^n+2n+1$ (`BoolCircuit.dnfDAG_size_le`). Together these give the claimed representation and bound.

**Key facts.** `BoolCircuit.dnfDAG_eval`, `BoolCircuit.dnfDAG_isFaninTwo`, `BoolCircuit.dnfDAG_size_le`.
