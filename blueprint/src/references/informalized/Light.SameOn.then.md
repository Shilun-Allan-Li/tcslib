<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Regions.lean :: Light.SameOn.then -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of agreement

**Claim.** If $\mu'$ agrees with $\mu$ on $K_1$, $\mu''$ agrees with $\mu'$ on $K_2$, and $K$ implies both predicates, then $\mu''$ agrees with $\mu$ on $K$.

**Proof.** Fix an index satisfying $K$. It satisfies both $K_1$ and $K_2$. The two agreement assumptions give $\mu''(b)=\mu'(b)$ and $\mu'(b)=\mu(b)$ there; transitivity of equality yields $\mu''(b)=\mu(b)$.
