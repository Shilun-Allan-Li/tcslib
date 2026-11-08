<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTime.lean :: Complexity.PolyTimeComputable.comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure under composition

**Claim.** If $f$ and $g$ are polynomial-time computable functions on bit strings, then their composition $g\circ f$ is polynomial-time computable.

**Proof.** Choose machines for $f$ and $g$, with running-time bounds $C(n+1)^c$ and $C'(n+1)^{c'}$. The second bound is monotone in the input length. The composition construction therefore computes $g(f(x))$ in time at most $a\bigl(C(n+1)^c+C'(C(n+1)^c+1)^{c'}+1\bigr)$ for some constant $a$. The polynomial bound `Complexity.comp_time_bound` bounds this by $a(C+C'(C+1)^{c'}+1)(n+1)^{\max(c,cc')}$. Hence the composed machine has a polynomial running-time bound, as required.

**Key facts.** `Turing.FinTM.computesFunInTime_comp`, `Turing.FinTM.ComputesInTime.mono`, `Complexity.comp_time_bound`.
