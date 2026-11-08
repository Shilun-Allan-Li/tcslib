<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.widthThreeTseitinCompletedAssignment_eq_local_of_mem_chain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Completed and Local Assignments

**Claim.** For any clause in the Tseitin chain formed from a chosen formula clause and its auxiliary literals, the completed assignment agrees with the local assignment for that chosen clause at every literal coordinate in the clause.

**Proof.** Fix a clause in the chain and a literal in that clause. The index-membership property of the Tseitin clause chain says that the literal's coordinate occurs either among the original lifted literals or among the auxiliary literals (index_mem_original_or_auxiliary_of_mem_tseitinClauseChain). Consider these two cases. If it is an original lifted coordinate, disjointness of the lifted-literal and auxiliary index lists ensures that the local filling procedure never changes that coordinate; the completed assignment also evaluates it by the original assignment, by the extension rule on original coordinates (extendCNFAssignment_castAdd). Thus the assignments agree there. If it is an auxiliary coordinate, write it as the coordinate indexed by a position in the auxiliary list. The completed assignment assigns that coordinate using the local assignment for the corresponding clause, by its definition through the clause-position equivalence; hence the two values agree. In both cases the claimed equality follows.

**Key facts.** `FABL.index_mem_original_or_auxiliary_of_mem_tseitinClauseChain`, `FABL.disjoint_tseitinLiftLiterals_tseitinAuxiliaryLiterals`, `FABL.extendCNFAssignment_castAdd`, `FABL.fillTseitinClauseAux_eq_of_not_mem`.
