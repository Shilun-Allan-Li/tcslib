<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/ThreeSATToClique.lean :: ThreeSATToClique.literalsConflict_symm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of literal conflict

**Claim.** For any two literals, the first conflicts with the second if and only if the second conflicts with the first.

**Proof.** There are four constructor combinations. If both literals have the same sign, neither ordering is a conflict. If their signs differ, conflict means that their variables are equal. Reversing the order preserves equality, so the conflict relation is symmetric.
