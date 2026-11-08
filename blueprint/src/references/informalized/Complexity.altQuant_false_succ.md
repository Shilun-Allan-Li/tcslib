<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Defs.lean :: Complexity.altQuant_false_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Alternating Successor Step

**Claim.** At $k+1$ rounds with initial universal quantification, the alternating predicate holds on $w$ exactly when for every binary string $u$ of length $m$, the $k$-round predicate with initial existential quantification holds on the pair encoding of $w$ and $u$.

**Proof.** Unfold the definition of the alternating predicate at the successor round. Its outer operation is the universal quantifier over strings $u$ of length $m$, and the predicate inside it is the alternating predicate at the remaining $k$ rounds with the initial quantifier switched from false to true. This is exactly the stated equivalence.
