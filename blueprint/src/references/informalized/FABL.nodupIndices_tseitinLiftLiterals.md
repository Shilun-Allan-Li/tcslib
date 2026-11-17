<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.nodupIndices_tseitinLiftLiterals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Lifted Literal Indices

**Claim.** If a DNF term has pairwise distinct literal indices, then its lifted literals also have pairwise distinct indices.

**Proof.** Lifting each literal sends its index through the map that includes the original $n$ coordinates into the larger set of $n+a$ coordinates. This inclusion is injective, so applying it to the term's list of distinct indices preserves the no-repetition property.
