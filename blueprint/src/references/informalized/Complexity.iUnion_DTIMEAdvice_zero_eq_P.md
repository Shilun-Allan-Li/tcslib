<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.iUnion_DTIMEAdvice_zero_eq_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Length Advice and Polynomial Time

**Claim.** The union over all $c$ of languages decidable with zero-length advice in time a constant multiple of $n^c+1$ is exactly the class $P$.

**Proof.** First note two elementary bounds, valid for all $c,n\in\mathbb{N}$: $n^c+1\le 2(n^{c+1}+1)$ and $n+1\le n^{c+1}+1$. The first follows by comparing powers when $n>0$, with $n=0$ checked directly; the second follows from $n\le n^{c+1}$, again including $n=0$. For the forward inclusion, start with a language witnessed at exponent $c$. The first bound and monotonicity of advice-time classes in the time bound (`DTIMEAdvice.mono_const`) allow replacing its bound by a constant multiple of $n^{c+1}+1$. The zero-advice characterization (`DTIMEAdvice_zero_eq_DTIME`), using the second bound, identifies this class with ordinary deterministic time at that polynomial bound. It therefore lies in $P$ by the inclusion of each such time class in $P$ (`dtime_poly_subset_P`). For the reverse inclusion, take a language in $P$, so it has a witness at some exponent $c$ and constant factor $a$. Move to exponent $c+1$; the first bound shows that time bounded by $a(n^c+1)$ is bounded by $(2a)(n^{c+1}+1)$. The zero-advice characterization converts this ordinary time witness into a zero-length advice witness. The stated monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`) underlies the time-bound enlargements.

**Key facts.** `Complexity.DTIMEAdvice.mono_const`, `Complexity.DTIMEAdvice_zero_eq_DTIME`, `Complexity.dtime_poly_subset_P`, `Turing.FinTM.ComputesInTime.mono`.
