<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.assignmentForTerm_blockCode_literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment Recovered from a Block Code

**Claim.** For a term of width at most $w$, a block code formed from an input’s adjusted bits on selected literal positions yields an assignment agreeing with the input at the coordinate of each selected literal.

**Proof.** The assignment constructed from the block code is equal to the assignment constructed directly from that block code for the term (`FABL.SwitchingBlockCode.assignmentForTerm_eq_assignmentOfBlock`). For each selected literal position, the latter assignment agrees with the original input at that literal’s coordinate (`FABL.DNFTerm.assignmentOfBlock_blockCode_literal`). Combining these equalities gives the asserted agreement.

**Key facts.** `FABL.SwitchingBlockCode.assignmentForTerm_eq_assignmentOfBlock`, `FABL.DNFTerm.assignmentOfBlock_blockCode_literal`.
