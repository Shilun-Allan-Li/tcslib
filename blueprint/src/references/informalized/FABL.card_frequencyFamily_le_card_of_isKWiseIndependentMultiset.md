<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.card_frequencyFamily_le_card_of_isKWiseIndependentMultiset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frequency family cardinality bound

**Claim.** If the sign vectors indexed by a finite nonempty set are $k$-wise independent in the stated Fourier sense, and every union of two sets in a family of coordinate subsets has size at most $k$, then the family has cardinality at most the size of the indexing set.

**Proof.** For each member $S$ of the family, the normalized restricted Walsh vector associated to $S$ gives a vector in a real vector space of functions on the finite indexing set. The orthonormality result for these vectors (normalizedRestrictedWalshVector_orthonormal) applies because the union of any two family members has size at most $k$ and the multiset satisfies the stated independence hypothesis. An orthonormal family is linearly independent. A linearly independent family in a finite-dimensional space has size at most the dimension of that space; here the space of real functions on the indexing set has dimension equal to its cardinality. Thus the family has at most as many members as there are indices.

**Key facts.** `FABL.normalizedRestrictedWalshVector_orthonormal`.
