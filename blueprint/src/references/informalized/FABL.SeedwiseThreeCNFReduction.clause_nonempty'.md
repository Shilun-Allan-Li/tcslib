<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.SeedwiseThreeCNFReduction.clause_nonempty' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty Indexed Clause

**Claim.** For any seed and any clause index, the selected clause contains at least one literal.

**Proof.** The selected clause belongs to the formula's clause list by the indexed-clause membership fact (`FABL.SeedwiseThreeCNFReduction.clause_mem`). The reduction guarantees that every clause in that list has positive width. Applying this condition to the selected clause shows that its width, the number of its literals, is positive.

**Key facts.** `FABL.SeedwiseThreeCNFReduction.clause_mem`.
