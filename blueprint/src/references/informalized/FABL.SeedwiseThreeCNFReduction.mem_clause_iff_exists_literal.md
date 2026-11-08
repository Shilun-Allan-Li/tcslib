<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.SeedwiseThreeCNFReduction.mem_clause_iff_exists_literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literal Occurrences in Short Clauses

**Claim.** A literal occurs in clause $q$ exactly when it is the literal at position $j$ modulo the clause width for some $j\in\{0,1,2\}$.

**Proof.** Suppose first that the literal occurs in the clause. The characterization of list membership by an indexed list entry gives a position $i$ whose entry is that literal. The width bound places $i$ among the first three positions. Choose $j=i$; since $i$ is less than the positive clause width, reducing $j$ modulo that width leaves the position unchanged, so the corresponding repeated-position literal is the given one. Conversely, every literal defined by such a modular position is an entry of the clause list, hence belongs to that list.

**Key facts.** `FABL.SeedwiseThreeCNFReduction.clause_width_le`, `FABL.SeedwiseThreeCNFReduction.clause_nonempty'`.
