<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.DisjointBlockChoices.blocks_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of each chosen block

**Claim.** For any valid sequence of $t$ successive disjoint choices of $d$-element subsets, every block in its associated list has cardinality $d$.

**Proof.** Induct on the number $t$ of choices. With no choices, the associated list is empty, so there is no block to check. For a positive number of choices, the choice consists of a first block followed by a valid sequence of the remaining choices. A block in the associated list is either this first block, whose membership in the $d$-element subsets of the remaining set gives cardinality $d$, or it belongs to the list from the remaining sequence. In the latter case the induction hypothesis gives the same cardinality.
