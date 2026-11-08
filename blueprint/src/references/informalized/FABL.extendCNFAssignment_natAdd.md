<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.extendCNFAssignment_natAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extension preserves auxiliary coordinates

**Claim.** In the concatenated assignment formed from an assignment on $n$ coordinates and an auxiliary assignment on $r$ coordinates, coordinate $n+j$ has the auxiliary assignment's value at $j$.

**Proof.** The extension indexes the concatenated assignment by applying the inverse sum-index equivalence and then selecting the corresponding summand. A coordinate represented by $n+j$ lies in the second block and corresponds to auxiliary index $j$. The extension therefore evaluates to the auxiliary assignment at $j$.
