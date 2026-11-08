<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.DisjointBlockChoices.blocks_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Chosen blocks lie in the original set

**Claim.** Every block in the list associated with a valid sequence of successive block choices is a subset of the original remaining set.

**Proof.** Induct on the number of choices, generalizing the original remaining set. With zero choices the list is empty, so the assertion holds. At a successor step, the first block belongs to the $d$-element subsets of the original remaining set, and hence is contained in it. Every later block is contained in the set remaining after the first block is removed, by the induction hypothesis. That set is itself a subset of the original remaining set, so every later block is also contained in the original set.
