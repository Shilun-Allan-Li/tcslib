<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Separation.lean :: Complexity.dtime_poly_ssubset_dtime_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial time is strictly below exponential time

**Claim.** For every natural number $k$, $\mathrm{DTIME}(n\mapsto n^k+1)$ is a proper subset of $\mathrm{DTIME}(n\mapsto 2^n)$.

**Proof.** Use the deterministic time hierarchy theorem in its positive-bound form (\texttt{time\_hierarchy\_of\_pos}) with $f(n)=n^k+1$ and $g(n)=2^n$. The exponential bound is time-constructible (\texttt{timeConstructible\_two\_pow}) and is positive for every $n$. The required eventual domination condition holds for every constant $A$: the eventual polynomial-square bound (\texttt{eventually\_poly\_sq\_le\_two\_pow}) gives $A(n^k+1+n+1)^2\le 2^n$ for all sufficiently large $n$, exactly the condition required by the hierarchy theorem. The theorem therefore yields the strict inclusion.

**Key facts.** `Complexity.timeConstructible_two_pow`, `Complexity.eventually_poly_sq_le_two_pow`, `Complexity.time_hierarchy_of_pos`.
