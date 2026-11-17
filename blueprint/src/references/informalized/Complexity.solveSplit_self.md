<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.solveSplit_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Solution of the Padding Equation

**Claim.** For all natural numbers $C,c,n$, the least $i$ in the search range satisfying $i+C(i+1)^c=n+C(n+1)^c$ is $n$.

**Proof.** The function $f(j)=j+C(j+1)^c$ is strictly increasing: if $a<b$, then $(a+1)^c\le(b+1)^c$, so multiplying by $C$ preserves the weak inequality, while the first summand increases strictly. At $i=n$, the equation holds by definition, and $n$ belongs to the search range $0,\ldots,n+C(n+1)^c$. Thus the search succeeds. Any returned index $j$ satisfies $f(j)=f(n)$; injectivity of a strictly increasing function forces $j=n$. Consequently the search returns $n$, which is the least satisfying index.
