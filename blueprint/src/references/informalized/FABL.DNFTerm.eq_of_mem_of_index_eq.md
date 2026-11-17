<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFTerm.eq_of_mem_of_index_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of literals by coordinate

**Claim.** If two literals in the same conjunction term have the same coordinate, then they are equal.

**Proof.** The list of coordinates obtained from the term’s literals has no repetitions. Therefore the map sending each literal in the term to its coordinate is injective on the term’s members. Since the two literals have the same coordinate, injectivity gives their equality.
