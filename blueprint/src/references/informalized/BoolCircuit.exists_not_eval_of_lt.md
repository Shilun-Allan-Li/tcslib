<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardFunctions.lean :: BoolCircuit.exists_not_eval_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hard functions for small circuit trees

**Claim.** If $(n+4)S<2^n$, then some Boolean function on $n$ input bits disagrees with every Boolean circuit tree of size at most $S$ on at least one input.

**Proof.** Let $T$ be the set of functions computed by circuit trees of size at most $S$. The counting estimate (`card_computable_le`) bounds $|T|$ by $2^{(n+4)S}$. The full space of Boolean functions on $n$ bits has $2^{2^n}$ elements. Since $(n+4)S<2^n$, raising $2$ to these exponents shows that $|T|<2^{2^n}$. Choose a function outside $T$. A tree agreeing with it on every input would compute that same function and put it in $T$, which is impossible; hence each size-bounded tree disagrees somewhere.

**Key facts.** `BoolCircuit.card_computable_le`.
