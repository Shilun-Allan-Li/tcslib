<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Lupanov.lean :: BoolCircuit.succ_sq_le_four_mul_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential bound for a square

**Claim.** For every natural number $n$, $(n+1)^2\le 4\cdot 2^n$.

**Proof.** For $n<2$, check $n=0$ and $n=1$ directly. For $n\ge2$, use induction starting at $2$. The base case is a direct calculation. For the successor step, rewrite $2^{m+1}=2\cdot2^m$ and use the induction hypothesis to bound the right-hand side by $8(m+1)^2$. The needed comparison $(m+2)^2\le 2(m+1)^2$ holds for $m\ge2$ (indeed, their difference is $m^2-2$), completing the induction.
