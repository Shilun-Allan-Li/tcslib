<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.SeedwiseThreeCNFReduction.clause_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership of an Indexed Clause

**Claim.** For any seed and any clause index, the clause selected by that index belongs to the reduction's formula for that seed.

**Proof.** The selected clause is the formula's clause at the given valid index. Every clause selected by `clauseAt` belongs to the formula's clause list (`FABL.CNFFormula.clauseAt_mem`), so the selected clause has the required membership.

**Key facts.** `FABL.CNFFormula.clauseAt_mem`.
