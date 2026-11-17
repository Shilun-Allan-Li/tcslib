<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.length_tseitinClauseTerms -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause terms preserve length

**Claim.** Under the stated distinctness and disjointness hypotheses, the number of Tseitin clause terms equals the number of clauses in the chain.

**Proof.** Each clause in the chain has pairwise distinct coordinates by the chain’s distinctness result. The term construction therefore maps every clause to a term carrying that same clause as its literal list, using the proof of distinctness to certify that it is a valid term. This mapping neither drops nor duplicates entries, so the resulting term list has the same length as the clause chain.
