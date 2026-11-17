<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.tseitinStep_invariants -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariants of a Tseitin step

**Claim.** The updated original list beginning with the negated auxiliary literal and followed by the third and fourth original literals has pairwise distinct indices; the remaining auxiliary list has pairwise distinct indices; and these two index sets are disjoint.

**Proof.** The negated auxiliary literal retains the auxiliary literal’s index. The original list’s distinctness therefore already ensures that the third and fourth literals, and all later original literals, have distinct indices from one another. Disjointness of the original and auxiliary index sets ensures that the auxiliary index differs from every index in the original list, in particular from the third and fourth indices. Thus adjoining the negated auxiliary literal preserves pairwise distinctness. Removing the first auxiliary literal from a pairwise-distinct auxiliary list preserves distinctness, and removing it from the set of auxiliary indices preserves disjointness from the updated original list. Negating a literal changes only its required sign, not its index, so these index arguments establish all three claims.
