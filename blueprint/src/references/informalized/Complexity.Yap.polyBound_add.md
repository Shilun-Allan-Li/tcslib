<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.polyBound_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of Polynomial Bounds

**Claim.** The sum of two polynomially bounded functions is polynomially bounded.

**Proof.** Choose bounds $f(n)\le A(n+1)^\alpha$ and $g(n)\le B(n+1)^\beta$. Set the new coefficient to $A+B$ and the new exponent to $\alpha+\beta$. Since $n+1\ge1$, increasing either exponent to $\alpha+\beta$ can only increase the corresponding power. Therefore both $(n+1)^\alpha$ and $(n+1)^\beta$ are at most $(n+1)^{\alpha+\beta}$. Adding the two original bounds gives $f(n)+g(n)\le(A+B)(n+1)^{\alpha+\beta}$ for every $n$, which is the required polynomial bound.
