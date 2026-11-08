<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.exactlyThreeCNF_clause_width_eq_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of padded clauses

**Claim.** Every clause in the exactly-three-literal conversion of a CNF formula of width at most three has width exactly three.

**Proof.** Membership in the converted formula means that the clause comes from padding some original clause. The original clause has width at most three: its width is bounded by the formula width, by the fact that every term's width is at most the width of its DNF formula (`FABL.DNFFormula.width_le_of_mem`), and the assumed formula-width bound. The padding-width theorem says that every clause produced from an original clause of width at most three has width exactly three (`FABL.exactlyThreePadClause_width_eq_three`). Applying it to the original clause and the given padded clause proves the claim.

**Key facts.** `FABL.DNFFormula.width_le_of_mem`, `FABL.exactlyThreePadClause_width_eq_three`.
