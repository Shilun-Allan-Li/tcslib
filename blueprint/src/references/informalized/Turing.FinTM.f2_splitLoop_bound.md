<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitLoop_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial loop bound

**Claim.** For all natural numbers $c,A,e,n$, $c(A(n+1)^{e+1}+1)(n+2)\le 2c(A+1)(n+1)^{e+2}$.

**Proof.** Since $(n+1)^{e+1}\ge 1$, we have $A(n+1)^{e+1}+1\le (A+1)(n+1)^{e+1}$. Also $n+2\le 2(n+1)$. Multiplying these inequalities by the nonnegative factors gives an upper bound of $c(A+1)(n+1)^{e+1}\,2(n+1)$. Combining the powers, $(n+1)^{e+1}(n+1)=(n+1)^{e+2}$, yields the claimed bound.
