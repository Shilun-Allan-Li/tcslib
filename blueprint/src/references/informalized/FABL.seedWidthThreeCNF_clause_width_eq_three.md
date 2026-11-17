<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.seedWidthThreeCNF_clause_width_eq_three -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause width in the three-width conversion

**Claim.** If $3\le r$, every clause in the converted seed acceptance CNF has width exactly $3$.

**Proof.** A clause in the converted formula belongs to the block produced from some clause of the original seed acceptance formula. Unpacking that block identifies it with a clause in the Tseitin chain built from the lifted original literals and the auxiliary literals for that block. The chain lemma says each such clause has length three, provided the original literal list has length equal to the auxiliary list's length plus three (`FABL.tseitinClauseChain_clause_length_eq_three`). The lifted list has the original clause's width as its length (`FABL.length_tseitinLiftLiterals`), and the auxiliary list has length $r-3$ (`FABL.length_tseitinAuxiliaryLiterals`). The original clause has width $r$: it is a clause of the truth-table CNF, whose clauses all have width $r$ (`FABL.truthTableCNF_clause_width`); its membership follows by taking the clause at its index (`FABL.CNFFormula.clauseAt_mem`). Hence the lifted length is $r=(r-3)+3$, as required, and the converted clause has width three.

**Key facts.** `FABL.CNFFormula.clauseAt_mem`, `FABL.truthTableCNF_clause_width`, `FABL.length_tseitinClauseChain_clause_length_eq_three`, `FABL.length_tseitinLiftLiterals`, `FABL.length_tseitinAuxiliaryLiterals`.
