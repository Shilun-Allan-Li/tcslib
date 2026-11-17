<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.altQuant_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alternating Quantifier Successor Step

**Claim.** For a language $V$, a length $m$, a starting quantifier $b$, a round count $k$, and a string $w$, the alternating predicate at $k+1$ rounds holds exactly when quantifying with $b$ over strings $u$ of length $m$ makes the $k$-round predicate with the opposite starting quantifier hold on the pair encoding of $w$ and $u$.

**Proof.** By definition, the predicate at $k+1$ rounds is the one-step quantifier operation with initial quantifier $b$, applied to the $k$-round predicate with initial quantifier $!b$ at the pair encoding of $w$ and the chosen string. This is precisely the right-hand side, so the two propositions are definitionally equal.
