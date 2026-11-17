<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Diagonal.lean :: Complexity.TimeHierarchy.le_sq_overhead -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic overhead dominates time

**Claim.** For all natural numbers $t,n$, we have $t\le(t+n+1)^2$.

**Proof.** Let $X=t+n+1$. Since $X\ge1$, we have $X\le X^2$ (equivalently, $X\le X\cdot X$). Also $t\le X$, so transitivity gives $t\le X^2$, as required.
