<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.uniformInner_le_uniformLpNorm_fourThird_mul_four -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Hölder inequality for exponents four-thirds and four

**Claim.** On a finite nonempty set, the uniform inner product of two real-valued functions is at most the product of their uniform $L^{4/3}$ and $L^4$ norms.

**Proof.** Let $N$ be the cardinality of $\Omega$, and let $A=\sum_x |f(x)|^{4/3}$ and $B=\sum_x |g(x)|^4$. Hölder's inequality for finite sums, with conjugate exponents $4/3$ and $4$, gives $\sum_x f(x)g(x)\le A^{3/4}B^{1/4}$. The uniform inner product is this sum divided by $N$. Meanwhile, the uniform norms are $(A/N)^{3/4}$ and $(B/N)^{1/4}$. Since their product is $(A^{3/4}B^{1/4})/N$, dividing the finite-sum inequality by the positive number $N$ proves the claim.
