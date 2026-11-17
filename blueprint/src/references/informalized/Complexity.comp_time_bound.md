<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTime.lean :: Complexity.comp_time_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed Time Budget Bound

**Claim.** For all natural numbers $a,C,c,C',c',n$, the composed time budget is bounded by $a\bigl(C+C'(C+1)^{c'}+1\bigr)(n+1)^{\max(c,cc')}.

**Proof.** Since $n+1$ is positive, $(n+1)^c\ge1$, so $(n+1)^c\le (n+1)^{\max(c,cc')}$. Also, $C(n+1)^c+1\le (C+1)(n+1)^c$. Raising this inequality to the power $c'$ and using the laws for powers of products gives $(C(n+1)^c+1)^{c'}\le (C+1)^{c'}(n+1)^{cc'}\le (C+1)^{c'}(n+1)^{\max(c,cc')}$. The constant term $1$ is bounded by the same dominating power. Multiplying these three bounds by their respective nonnegative coefficients $C$, $C'$, and $1$, adding them, and finally multiplying by $a$ gives the result after factoring out $(n+1)^{\max(c,cc')}$.
