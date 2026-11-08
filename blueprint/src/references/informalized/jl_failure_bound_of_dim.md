<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean :: jl_failure_bound_of_dim -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension Threshold Bounds Failure

**Claim.** If $\varepsilon>0$, $n\ge2$, and $k\ge32\log(n)/\varepsilon^2$, then $k>0$ and $|V|^2\,2\exp(-k\varepsilon^2/8)<1$ whenever $|V|\le n$.

**Proof.** The dimension assumption implies $k\varepsilon^2/8\ge4\log n$. Since $n\ge2$, this also implies $k>0$. Exponentiating the first inequality gives $\exp(-k\varepsilon^2/8)\le n^{-4}$. From $|V|\le n$, we have $|V|^2\le n^2$, so the expression in question is at most $2n^2n^{-4}=2/n^2$. As $n\ge2$, this is at most $1/2$, which is strictly less than $1$.
