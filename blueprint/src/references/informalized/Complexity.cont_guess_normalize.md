<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_guess_normalize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Nondeterministic Time Normalization

**Claim.** If a finite nondeterministic machine decides $L$ within time $K(n+C(n+1)^c+1)^r$, then $L$ belongs to $\bigcup_{e\in\mathbb N}\mathrm{NTIME}(n^e+1)$.

**Proof.** Choose exponent $e=r\max(1,c)$ and enlarge the time coefficient to $K(C+1)^r2^e$. The polynomial bound gives, for every input length $n$, $K(n+C(n+1)^c+1)^r\le K(C+1)^r2^e(n^e+1)$ (`cont_guess_time_bound`). The original machine halts on every choice word within its given bound, so it still halts within the enlarged bound by monotonicity (`Turing.NDTM.HaltsWithin.mono`). Because all choice words halt by the original bound, extending the choice length preserves whether an accepting computation exists (`acceptsWithin_iff_of_halts`). Hence the machine decides the same language within the normalized polynomial bound, establishing membership in the indicated union.

**Key facts.** `Complexity.cont_guess_time_bound`, `Turing.NDTM.HaltsWithin.mono`, `Complexity.acceptsWithin_iff_of_halts`.
