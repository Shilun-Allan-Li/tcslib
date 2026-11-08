<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Lupanov.lean :: BoolCircuit.exists_dagCircuit_faninTwo_mul_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small fan-in-two circuit

**Claim.** For every Boolean function on $n$ input variables, there is a well-formed acyclic circuit computing it, with at most two inputs per gate, and with $(n+1)$ times its size at most $40\cdot 2^n$.

**Proof.** Choose the Lupanov circuit with parameter $k=\lfloor\log_2 n\rfloor-1$, represented in the proof as $\mathrm{Nat.log}\,2\,n-1$. The elementary inequality $\mathrm{Nat.log}\,2\,n-1\le n$ makes this parameter admissible. The Lupanov construction computes the given function (`BoolCircuit.Lupanov.lupDAG_eval`) and is well-formed with fan-in at most two (`BoolCircuit.Lupanov.lupDAG_isFaninTwo`). Its size is at most $2n+4\cdot 2^{n-k}+2\cdot 2^k+2^{2^k}$ (`BoolCircuit.Lupanov.lupDAG_size_le`). Multiplying this estimate by $n+1$ and applying the numerical bound for this choice of $k$ (`BoolCircuit.lupanov_arith`) yields $(n+1)$ times the circuit size at most $40\cdot 2^n$.

**Key facts.** `BoolCircuit.Lupanov.lupDAG_eval`, `BoolCircuit.Lupanov.lupDAG_isFaninTwo`, `BoolCircuit.Lupanov.lupDAG_size_le`, `BoolCircuit.lupanov_arith`.
