<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.polyTimeComputable_or -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjunction preserves polynomial-time computability

**Claim.** If the one-bit output functions for Boolean predicates $p$ and $q$ are polynomial-time computable, then so is the one-bit output function for their disjunction.

**Proof.** Use polynomial-time closure under a Boolean conditional with predicate $p$, outputting the constant word $[\mathrm{true}]$ when $p(x)$ is true and using the polynomial-time computation of $q(x)$ otherwise. If $p(x)$ is true, the output is true; if it is false, the output is $q(x)$. In either case the result is $p(x)\lor q(x)$, and the constant branch and the given computation of $q$ are polynomial-time computable.

**Key facts.** `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_ite`.
