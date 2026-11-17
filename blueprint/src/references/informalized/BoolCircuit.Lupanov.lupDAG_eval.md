<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Lupanov.lean :: BoolCircuit.Lupanov.lupDAG_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the constructed circuit

**Claim.** For every Boolean function $f$ on $n$ bits and every $k\le n$, the circuit constructed from $f$ and $k$ outputs $f(x)$ on each input $x$.

**Proof.** The specification of the appended OR tree says that its output has the same value as the OR gate applied to the values at the combining roots, evaluated in the original gate list (the output-value clause of `lupGates_spec`). The roots are exactly the vertices whose values are disjoined by `any_comb`, which identifies that disjunction with $f(x)$. Thus the circuit output equals $f(x)$.

**Key facts.** `BoolCircuit.Lupanov.lupGates_spec`, `BoolCircuit.Lupanov.any_comb`.
