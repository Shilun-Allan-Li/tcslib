<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.DTIME_subset_SPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Time Is Bounded Space

**Claim.** For every time bound $T$, every language decidable in deterministic time bounded by a constant multiple of $T$ is decidable using space bounded by a constant multiple of $T$.

**Proof.** First consider the possibility that $T(n)=0$ at some length. Then `DTIME_eq_empty_of_exists_zero` makes the deterministic time class empty, so the inclusion holds immediately. Otherwise, $T(n)\ge 1$ for every $n$. Let a machine with $k$ work tapes decide a language in time $cT$. On each input $x$, use that computation as the space decider and take its running time $cT(|x|)$ as the witnessing time. The bound `spaceUsed_le_mul_succ` says that by time $t$ the machine has used at most $k(t+1)$ space. Hence its space is at most $k(cT(|x|)+1)=kcT(|x|)+k$. Since $T(|x|)\ge1$, this is at most $(kc+k)T(|x|)$. The latter is the required constant multiple of $T$.

**Key facts.** `Complexity.DTIME_eq_empty_of_exists_zero`, `Turing.MultiTapeTM.spaceUsed_le_mul_succ`.
