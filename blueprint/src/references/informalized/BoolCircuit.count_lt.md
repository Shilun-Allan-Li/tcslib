<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGHardFunctions.lean :: BoolCircuit.count_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit-counting inequality

**Claim.** For natural numbers $n,S$ with $1\le n$ and $10nS\le 2^n$, one has $(S+1)\bigl(3(S+1)^2\bigr)^S S<2^{2^n}$.

**Proof.** If $S=0$, the left side is zero, so the strict inequality follows since the right side is positive. Suppose then that $S>0$. First bound the expression by $(2(S+1))^{2(S+1)}$: regroup its factors as $((S+1)S)(3(S+1)^2)^S$, use $(S+1)S\le (2(S+1))^2$ and $3(S+1)^2\le (2(S+1))^2$, and combine the powers. The hypotheses and $S>0$ give $2(S+1)\le 2^n$ and $n\,2(S+1)<2^n$. Raising the first inequality to the exponent $2(S+1)$ bounds the expression by $(2^n)^{2(S+1)}=2^{n\,2(S+1)}$. The second inequality makes this strictly less than $2^{2^n}$, since powers of $2$ are strictly increasing in their natural-number exponents.
