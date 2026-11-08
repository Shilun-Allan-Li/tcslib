<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPOperator.lean :: Randomized.subset_BPdot -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inclusion in randomized closure

**Claim.** For any set $\mathcal C$ of languages, every language in $\mathcal C$ belongs to the class of languages that reduce randomly to some member of $\mathcal C$.

**Proof.** Take any language $L\in\mathcal C$. It reduces randomly to itself by the identity reduction (`Randomized.RandReducible.refl`). Thus $L$ is a witness for membership in the randomized closure: it belongs to $\mathcal C$, and the required reduction holds. This proves the inclusion.

**Key facts.** `Randomized.RandReducible.refl`.
