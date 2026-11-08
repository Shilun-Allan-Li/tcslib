<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/VarianceSensitiveLargeCoefficient.lean :: FABL.mem_varianceLargeCoeffFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Large Coefficient Family Characterization

**Claim.** A set $S$ belongs to the large-coefficient family for $f$ exactly when it is contained in the selected Friedgut coordinates, has cardinality at most the variance-based Friedgut degree, and is nonempty.

**Proof.** Membership in the large-coefficient family means membership in the low-degree subsets, with the empty set erased. By the characterization of low-degree subsets (FABL.mem_lowDegreeSubsets), membership in that family is equivalent to the two conditions that $S$ is contained in the selected coordinates and that its cardinality is at most the degree. Erasing the empty set adds exactly the further condition $S\ne\varnothing$. Combining these conditions gives the stated equivalence.

**Key facts.** `FABL.mem_lowDegreeSubsets`.
