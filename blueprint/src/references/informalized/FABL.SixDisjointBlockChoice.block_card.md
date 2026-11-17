<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.SixDisjointBlockChoice.block_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Chosen Block Cardinality

**Claim.** Each block selected by a six-disjoint-block choice has cardinality $d$.

**Proof.** The block at position $i$ is the element of the choice's block list at index $i$. That indexed element belongs to the list. Every block occurring in a disjoint-block choice has cardinality $d$ (`DisjointBlockChoices.blocks_card`), so the chosen block does as well.

**Key facts.** `FABL.DisjointBlockChoices.blocks_card`.
