<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.DisjointBlockChoices.blocks_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the chosen block list

**Claim.** The list associated with any valid sequence of $t$ block choices has length exactly $t$.

**Proof.** Induct on $t$. At zero choices the associated list is empty, hence has length zero. At a successor step, the choice consists of a first block and a valid sequence of $t$ further choices, and its list is that first block followed by the list for the remaining sequence. The induction hypothesis gives length $t$ for the latter list; adjoining the first block makes the total length $t+1$.
