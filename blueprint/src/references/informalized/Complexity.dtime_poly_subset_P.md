<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/P.lean :: Complexity.dtime_poly_subset_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-degree polynomial time lies in P

**Claim.** For every natural number $c$, the languages decidable within a constant multiple of $n^c+1$ steps belong to $\mathsf{P}$.

**Proof.** By definition, $\mathsf{P}$ is the union, over all natural exponents, of the corresponding deterministic time classes. A language in the class for the fixed exponent $c$ therefore belongs to this union by its $c$th component, which is precisely the asserted inclusion.
