<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Diagonal.lean :: Complexity.TimeHierarchy.DiagSimulator.time_hierarchy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Time Hierarchy

**Claim.** Under the stated assumptions, DTIME$(f)$ is a proper subset of DTIME$(g+1)$.

**Proof.** First prove the inclusion. Choose a threshold $N$ beyond which $\Phi(f(n),n)\le g(n)$, using the growth assumption with multiplier $1$. Let $F=\sum_{i<N}f(i)$. For $n<N$, we have $f(n)\le F$; for $n\ge N$, the bound $f(n)\le\Phi(f(n),n)\le g(n)$ follows from the lower bound on $\Phi$. Thus for every $n$, $f(n)\le(F+1)(g(n)+1)$. If a machine decides a language in DTIME$(f)$ with bound $c f(n)$, multiplying this pointwise estimate by $c$ shows that the same machine decides it within $c(F+1)(g(n)+1)$ steps. Hence DTIME$(f)\subseteq$ DTIME$(g+1)$. For strictness, suppose the inclusion were equality. The diagonal language for the simulator belongs to DTIME$(g+1)$ by the time-constructibility result `diagLangOf_mem_DTIME`; equality would therefore put it in DTIME$(f)$. But the growth assumption also gives, for every $A$ and every threshold $N_0$, an $n\ge N_0$ with $A\Phi(f(n),n)\le g(n)$. The diagonal nonmembership theorem `diagLang_not_mem_DTIME` then says that this language is not in DTIME$(f)$, a contradiction. Therefore the inclusion is proper.

**Key facts.** `Turing.FinTM.ComputesInTime.mono`, `Complexity.TimeHierarchy.diagLangOf_mem_DTIME`, `Complexity.TimeHierarchy.DiagSimulator.diagLang_not_mem_DTIME`.
