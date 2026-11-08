<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.DNFTerm.notFalsified_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of a Nonfalsified Term

**Claim.** The indicator that a term is not falsified by a restriction assignment is true exactly when every literal in the term is not falsified by that assignment.

**Proof.** A term is not falsified precisely when no literal in its list is falsified. Equivalently, there is no list element whose falsification test is true, which says that every literal in the list has falsification test false. This equivalence also covers the empty list: it has no falsified literal, and the universal condition holds vacuously.
