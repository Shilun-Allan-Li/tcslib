<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.literalListsHold_iff_tseitinClauseTerms -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction of Generated Clauses

**Claim.** Under the stated distinctness and disjointness assumptions on the literal indices, every clause in the Tseitin chain contains a literal satisfied by the assignment if and only if every corresponding clause term evaluates to $-1$.

**Proof.** For the forward direction, take a generated clause term. By the definition of the term list as a partial map over the clause chain, each such term comes from a clause in the chain and carries that clause's literals. The characterization of clause evaluation (`CNFFormula.clauseEval_eq_neg_one_iff`) turns satisfaction of that clause into evaluation equal to $-1$. Conversely, take any clause in the chain. The distinctness result (`tseitinClauseChain_nodupIndices`) supplies the condition needed to make it a clause term. That term occurs in the generated list, and the assumed evaluation condition, again by the clause-evaluation characterization, says the original clause contains a satisfied literal. This proves both implications.

**Key facts.** `FABL.tseitinClauseChain_nodupIndices`, `FABL.CNFFormula.clauseEval_eq_neg_one_iff`.
