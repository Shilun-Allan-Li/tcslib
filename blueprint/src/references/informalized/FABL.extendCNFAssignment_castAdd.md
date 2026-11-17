<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.extendCNFAssignment_castAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extension preserves original coordinates

**Claim.** In the concatenated assignment formed from an assignment on $n$ coordinates and an auxiliary assignment on $r$ coordinates, each coordinate $i<n$ retains its original assigned value.

**Proof.** The extension sends a coordinate of the concatenated index set back through the inverse of the sum-index equivalence, then selects from the original assignment or the auxiliary one according to which summand contains the index. A coordinate in the first block, represented by $i<n$, corresponds to the original summand with index $i$. Evaluating the extension there therefore gives the original assignment's value at $i$.
