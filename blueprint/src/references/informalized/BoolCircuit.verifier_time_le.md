<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard.lean :: BoolCircuit.verifier_time_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomially Scaled Verifier Time Bound

**Claim.** For all natural numbers $n,C,c,C_V,d$, the verifier time expression satisfies $C_V\bigl(n+C(n+1)^c+1\bigr)^d\leq\bigl(C_V(C+1)^d+1\bigr)(n+1)^{(c+1)d}$.

**Proof.** First bound the expression inside the power. Since $n+1\leq(n+1)^{c+1}$ and $(n+1)^c\leq(n+1)^{c+1}$, we have
\[
n+C(n+1)^c+1\leq (C+1)(n+1)^{c+1}.
\]
Raising both sides to the $d$th power preserves the inequality, and multiplication by $C_V$ does as well. The resulting right-hand side is $C_V(C+1)^d(n+1)^{(c+1)d}$, using the laws of natural-number powers. Finally, this is at most the claimed bound because $C_V(C+1)^d\leq C_V(C+1)^d+1$.
