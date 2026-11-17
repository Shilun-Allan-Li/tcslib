<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.dropValues_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Drop Values

**Claim.** If each of $n,p,z,s,u,f,q,t,a$ is at most $B$, then every entry of the vector $(p,n,z,s,u,f,q,t,a)$ is at most $B$.

**Proof.** The vector has exactly the nine entries $p,n,z,s,u,f,q,t,a$. The hypotheses give the required bound for each entry individually, so every coordinate is at most $B$.
