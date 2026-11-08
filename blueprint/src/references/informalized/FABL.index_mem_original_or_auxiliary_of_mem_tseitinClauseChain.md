<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.index_mem_original_or_auxiliary_of_mem_tseitinClauseChain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indices in a Tseitin clause chain

**Claim.** Every literal in a clause of the generated Tseitin clause chain has an index occurring among the original literals or the auxiliary literals.

**Proof.** We split according to the list shapes that determine the clause chain. When there are at least four original literals and at least one auxiliary literal, the first clause consists of the first two original literals and the first auxiliary literal. A literal in that clause therefore has its index among the originals or auxiliaries. Any later clause belongs to the chain formed recursively from the negation of that auxiliary literal followed by the remaining original literals, together with the remaining auxiliaries. By induction, its literal's index occurs in one of those lists. Negating a literal leaves its index unchanged; thus an index arising from the negated auxiliary is an original auxiliary index, while an index arising from the remaining originals or auxiliaries is already in the corresponding original list. If there are at least four originals but no auxiliaries, the chain is the single clause consisting of the originals, so the conclusion follows directly. With fewer than four originals, the chain is the single clause consisting of the original list; this also covers the empty list, where there can be no literal in the clause. In each case the claimed index membership follows.
