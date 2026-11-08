<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.tseitinClauseChain_nodupIndices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct indices in the clause chain

**Claim.** If the original literals have pairwise distinct indices, the auxiliary literals have pairwise distinct indices, and the two index sets are disjoint, then every clause in their Tseitin clause chain has pairwise distinct indices.

**Proof.** Use induction on the recursive construction of the chain. When there are at least four original literals and an auxiliary literal, the step-invariant lemma shows that the next original list, which begins with the negation of that auxiliary literal followed by the third and fourth original literals, has pairwise distinct indices; it also preserves distinctness of the remaining auxiliaries and disjointness of the two lists (`tseitinStep_invariants`). The first clause consists of the first two original literals and the auxiliary literal. Their indices are distinct because the original list is internally distinct and its indices are disjoint from the auxiliary list. The induction hypothesis applied to the next two lists gives pairwise distinct indices in every remaining clause. In all terminal cases the chain contains only the current original list, whose indices are distinct by the hypothesis.

**Key facts.** `FABL.tseitinStep_invariants`.
