<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_and -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conjunction of Polynomial-Time Predicates

**Claim.** If the one-bit functions for predicates $p$ and $q$ are polynomial-time computable, then the one-bit function for their conjunction is polynomial-time computable.

**Proof.** Apply the closure property for conjunction of polynomial-time predicates to the given machines for $p$ and $q$. It yields a polynomial-time machine whose one-bit output records $p(x)\wedge q(x)$ for each input $x$.

**Key facts.** `Complexity.polyTimeComputable_and`.
