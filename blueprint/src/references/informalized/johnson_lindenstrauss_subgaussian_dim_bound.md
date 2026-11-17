<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean :: johnson_lindenstrauss_subgaussian_dim_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Eventual dimension bound

**Claim.** For every positive ε below one and every $n\ge2$, there is a dimension threshold such that every dimension at least that threshold admits the asserted embedding for every set of at most $n$ points.

**Proof.** Choose the threshold to be the ceiling of $32\log(n)/\varepsilon^2$. For any integer dimension $k$ at least this ceiling, the defining property of the ceiling gives $32\log(n)/\varepsilon^2\le k$. The dimension-bound Johnson–Lindenstrauss theorem then applies to any ambient dimension and any finite set of at most $n$ points, giving the required linear embedding.

**Key facts.** `johnson_lindenstrauss_subgaussian`.
