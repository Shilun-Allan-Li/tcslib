<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Poly_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sums of Polynomially Bounded Functions

**Claim.** If $f$ and $g$ are polynomially bounded functions on the natural numbers, then their sum is polynomially bounded.

**Proof.** Choose constants $a,d$ and $b,e$ so that $f(n)\le a(n+1)^d$ and $g(n)\le b(n+1)^e$. Since $n+1\ge1$, increasing either exponent can only increase the corresponding power. Thus both powers are bounded by $(n+1)^{d+e}$, and adding the two inequalities gives $f(n)+g(n)\le(a+b)(n+1)^{d+e}$. This is a polynomial bound for the sum.
