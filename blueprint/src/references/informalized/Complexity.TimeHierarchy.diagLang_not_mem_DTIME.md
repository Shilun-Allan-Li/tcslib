<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Diagonal.lean :: Complexity.TimeHierarchy.diagLang_not_mem_DTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Diagonal language separation

**Claim.** Under the stated growth condition, the language of inputs on which the fixed diagonal machine does not output the single bit $1$ within $g(n)$ steps is not in $\mathrm{DTIME}(T)$.

**Proof.** Apply the diagonal simulator separation theorem (\texttt{Complexity.TimeHierarchy.DiagSimulator.diagLang_not_mem_DTIME}) to the fixed simulator used to define the diagonal language. Its growth hypothesis has the form $A\Phi(T(n),n)\le g(n)$; for this simulator, the relevant overhead is quadratic in $T(n)+n+1$. The assumed condition supplies that bound for every constant $A$ and arbitrarily large $n$. The theorem therefore rules out every machine deciding this language within a constant multiple of $T(n)$, which is exactly nonmembership in $\mathrm{DTIME}(T)$.

**Key facts.** `Complexity.TimeHierarchy.DiagSimulator.diagLang_not_mem_DTIME`.
