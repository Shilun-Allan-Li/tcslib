<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.card_e3LinConstraintClauses -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause count for a linear constraint

**Claim.** For any constraint requiring three distinct variables over the two-element field, the multiset of three-literal E3-SAT constraints constructed from it has cardinality $4$.

**Proof.** The clause multiset is the image, as a multiset, of the full finite set of indices in $\mathrm{Fin}\,4$ under the map that constructs a clause from each index. Since the domain has four elements, its mapped multiset has cardinality four; mapping preserves multiset cardinality even if some resulting clauses coincide.
