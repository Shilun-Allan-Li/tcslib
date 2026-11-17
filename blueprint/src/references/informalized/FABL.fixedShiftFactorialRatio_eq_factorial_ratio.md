<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.fixedShiftFactorialRatio_eq_factorial_ratio -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Factorial Formula for the Product

**Claim.** The product of $(m+i+1)/(m+3d+i+1)$ for $0\le i<3d$ equals $((m+3d)!)^2/((m+6d)!\,m!)$.

**Proof.** Separate the product of quotients into a quotient of products. The numerator product is the rising factorial with initial value $m+1$ and length $3d$; the denominator product is the rising factorial with initial value $m+3d+1$ and the same length. The identity relating factorials to rising factorials gives $m!$ times the numerator rising factorial equal to $(m+3d)!$, and $(m+3d)!$ times the denominator rising factorial equal to $(m+6d)!$. Substituting these identities into the quotient and rearranging yields the stated formula. The factorials involved are nonzero, so the divisions are valid.
