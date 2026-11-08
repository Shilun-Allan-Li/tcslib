<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Collapse.lean :: Complexity.mem_SigmaP_two_iff_exists_forall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existential-universal characterization of the second level

**Claim.** A language is in the second existential level exactly when it has polynomially bounded witnesses $u$ such that every same-length string $v$ makes the twice-encoded input belong to a polynomial-time language.

**Proof.** At two alternations, the defining predicate for the existential level first chooses a string $u$ of the prescribed length and then universally quantifies over strings $v$ of that same length. At the terminal level, the alternating predicate is simply membership in the polynomial-time language. Unfolding this definition at depth two gives exactly the displayed existential-universal condition, so the two propositions are definitionally equal.
