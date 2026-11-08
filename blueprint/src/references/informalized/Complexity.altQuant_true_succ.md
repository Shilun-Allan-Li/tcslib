<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.altQuant_true_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existential Alternating Successor Step

**Claim.** For a language $V$, length $m$, round count $k$, and string $w$, the alternating predicate at $k+1$ rounds starting existentially holds exactly when some string $u$ of length $m$ makes the $k$-round predicate starting universally hold on the pair encoding of $w$ and $u$.

**Proof.** Unfolding the successor clause of the alternating predicate with initial quantifier true gives the one-step quantifier operation for strings of length $m$, applied to the predicate with initial quantifier false at the corresponding pair encoding. By the definition of the one-step operation, the true case is existential quantification together with the length condition. This is exactly the asserted equivalence.
