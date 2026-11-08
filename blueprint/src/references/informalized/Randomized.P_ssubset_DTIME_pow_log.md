<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.P_ssubset_DTIME_pow_log -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Time Hierarchy Inclusion

**Claim.** The class of languages decidable in polynomial time is a proper subset of the class decidable in time $n^{\log_2 n}$ up to a constant multiplicative factor.

**Proof.** For containment, take a language in $P$ and choose an exponent $k$ witnessing its membership in the union defining $P$. The bound $n^k+1\le (2^{k^2}+2)n^{\log_2 n}$ shows that its polynomial-time decider also runs within a constant multiple of the quasi-polynomial bound. Monotonicity of deterministic time classes and absorption of a constant time factor into the class give the desired inclusion. (The numerical inequality is `pow_add_one_le_pow_log`; the class facts are `DTIME.mono` and `DTIME_const_mul_subset`.)

To prove the inclusion is strict, use the diagonal language for the time-constructible budget `quasiPolyBudget`. That language belongs to the target class: it is decidable in time `quasiPolyBudget n + 1`, which is at most $3n^{\log_2 n}$ (`diagLang_mem_DTIME`, `quasiPolyBudget_add_one_le`, and `DTIME_const_mul_subset`). If it belonged to $P$, it would lie in `DTIME (n^k + 1)` for some $k$. The diagonal nonmembership criterion says it suffices, for every constant $A$ and threshold $N$, to find $n\ge N$ with $A(n^k+n+2)^2\le\texttt{quasiPolyBudget}(n)$. Choose $n=2^m$ with $m=\max(N,A+2k+6)$. Then $n\ge N$, and `poly_sq_le_quasiPolyBudget` gives exactly the required inequality. This contradicts the assumed membership in the polynomial-time class, proving properness.

**Key facts.** `Randomized.pow_add_one_le_pow_log`, `Complexity.DTIME.mono`, `Randomized.DTIME_const_mul_subset`, `Complexity.TimeHierarchy.diagLang_mem_DTIME`, `Randomized.quasiPolyBudget_add_one_le`, `Randomized.timeConstructible_quasiPolyBudget`, `Randomized.quasiPolyBudget_add_one_le`, `Randomized.DTIME_const_mul_subset`, `Complexity.TimeHierarchy.diagLang_not_mem_DTIME`, `Randomized.poly_sq_le_quasiPolyBudget`.
