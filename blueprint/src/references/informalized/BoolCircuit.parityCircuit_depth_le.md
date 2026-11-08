<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.parityCircuit_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity circuit depth bound

**Claim.** For every natural number $n$, the depth of the parity circuit on $n$ variables is at most $4(\mathrm{Nat.log}\,2\,n+1)$.

**Proof.** The depth bound for the fuelled XOR construction (`BoolCircuit.xorFuel_depth`) bounds the depth of either output by the input pairs' maximum pair depth plus $2$ times the ceiling of the base-$2$ logarithm of the list length, plus $2$. The parity circuit is the first output for the parity-pair list. That list has length $n$ (`BoolCircuit.length_parityPairs`) and pair depth $0$ (`BoolCircuit.pairDepth_parityPairs`), so its depth is at most $2\,\mathrm{Nat.clog}\,2\,n+2$. The ceiling logarithm is at most the natural logarithm plus one: indeed, the strict inequality $n<2^{\mathrm{Nat.log}\,2\,n+1}$ implies the corresponding ceiling-log bound. Substituting gives a bound no larger than $4(\mathrm{Nat.log}\,2\,n+1)$, as claimed.

**Key facts.** `BoolCircuit.xorFuel_depth`, `BoolCircuit.pairDepth_parityPairs`, `BoolCircuit.length_parityPairs`.
