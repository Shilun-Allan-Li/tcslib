<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.altQuant_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Round Alternating Predicate

**Claim.** For any language $V$, length $m$, starting quantifier $b$, and string $w$, the alternating predicate at zero rounds holds exactly when $w\in V$.

**Proof.** At zero rounds the alternating predicate is defined to be membership in $V$, independently of the starting quantifier and the length parameter. Thus the equivalence is immediate from the base clause of its definition.
