<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.mem_P_of_polyTimeReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Polynomial-Time Reductions

**Claim.** If $L$ is polynomial-time many-one reducible to $L'$ and $L'\in\mathsf{P}$, then $L\in\mathsf{P}$.

**Proof.** Unpack the reduction as a polynomial-time computable map $f$ such that $x\in L$ exactly when $f(x)\in L'$. By the polynomial-time characterization of $L'\in\mathsf{P}$ (`Complexity.mem_P_iff`), its indicator is polynomial-time computable. Composing this indicator computation with $f$ is again polynomial-time computable (`Complexity.PolyTimeComputable.comp`); the reduction equivalence ensures that its output is precisely the indicator of $L$. Hence a machine decides $L$ within a bound of the form $A(n+1)^d$, so $L$ is in deterministic time with that bound. The estimate $(n+1)^d\le 2^d(n^d+1)$ (`Complexity.succ_pow_le`) puts this bound below $A2^d(n^d+1)$, and `Complexity.mem_P_of_dtime_le` concludes that $L\in\mathsf{P}$.

**Key facts.** `Complexity.mem_P_iff`, `Complexity.PolyTimeComputable.comp`, `Complexity.succ_pow_le`, `Complexity.mem_P_of_dtime_le`.
