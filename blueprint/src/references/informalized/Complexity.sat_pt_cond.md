<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_cond -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Conditional Function

**Claim.** If the one-bit function for $p$ and the functions $f$ and $g$ are polynomial-time computable, then the function returning $f(x)$ when $p(x)$ holds and $g(x)$ otherwise is polynomial-time computable.

**Proof.** Use the closure property for a conditional function: a polynomial-time computation of the predicate bit can select between the polynomial-time computations of $f$ and $g$. The resulting computation returns the specified branch on every input and remains polynomial-time.

**Key facts.** `Complexity.polyTimeComputable_ite`.
