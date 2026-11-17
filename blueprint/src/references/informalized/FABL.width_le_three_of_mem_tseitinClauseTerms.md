<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.width_le_three_of_mem_tseitinClauseTerms -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of a Tseitin Clause Term

**Claim.** If the original and auxiliary literal lists have pairwise distinct indices, disjoint index sets, and the original list has length at most the auxiliary-list length plus three, every term in the Tseitin clause terms has width at most three.

**Proof.** Membership in the Tseitin clause terms means that the term is the term associated with some clause in the Tseitin clause chain; the term's literal list is precisely that clause. The chain-length bound says that every such clause has length at most three under the assumed capacity inequality (length_le_three_of_mem_tseitinClauseChain). Since term width is the length of its literal list, the result follows.

**Key facts.** `FABL.length_le_three_of_mem_tseitinClauseChain`.
