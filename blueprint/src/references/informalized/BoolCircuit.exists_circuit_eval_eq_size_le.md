<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Universal.lean :: BoolCircuit.exists_circuit_eval_eq_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small tree representation

**Claim.** For every Boolean function on assignments to $n$ variables, there is a Boolean circuit tree computing it on every assignment and having size at most $2^n(n+1)+1$.

**Proof.** Take the universal circuit tree associated with the given function. Its evaluation agrees with the function on every assignment, by the universal circuit evaluation theorem (`BoolCircuit.universalCircuit_eval`). Its size satisfies the stated bound by the universal circuit size estimate (`BoolCircuit.universalCircuit_size_le`). These two properties give the required tree.

**Key facts.** `BoolCircuit.universalCircuit_eval`, `BoolCircuit.universalCircuit_size_le`.
