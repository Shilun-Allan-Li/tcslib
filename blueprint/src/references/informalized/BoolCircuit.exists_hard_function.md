<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardFunctions.lean :: BoolCircuit.exists_hard_function -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of a hard Boolean function

**Claim.** For every $n$, there is a Boolean function on $n$ input bits such that every circuit tree of size at most $2^n/(n+5)$ disagrees with it on some input.

**Proof.** Apply the counting result that produces a function missed by every tree of size at most $S$, provided $(n+4)S<2^n$ (`BoolCircuit.exists_not_eval_of_lt`), with $S=2^n/(n+5)$. If this quotient is zero, the required strict inequality follows immediately because $2^n$ is positive. If it is positive, then $n+4<n+5$ gives $(n+4)S<(n+5)S$. Since $S$ is the quotient, $(n+5)S\le 2^n$ by the defining property of natural-number division. Hence $(n+4)S<2^n$, so the counting result supplies the desired hard function.

**Key facts.** `BoolCircuit.exists_not_eval_of_lt`.
