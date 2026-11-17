<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFTerm.positionOfSupport_literal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Position of a Supported Literal

**Claim.** For every valid position in the literal list, the position selected for the coordinate of the literal at that position is that same position.

**Proof.** Let $j$ be a valid position and consider the coordinate of its literal. That coordinate belongs to the support because the literal occurs in the list (`mem_support_of_mem_literals`). The position selected for this coordinate retrieves a literal with the same coordinate, by the result that the selected literal has the coordinate used to select it (`positionOfSupport_index`). The original literal at $j$ also has that coordinate. Since the term's literal indices are pairwise distinct, two valid positions with the same literal coordinate must be equal. Hence the selected position is $j$.

**Key facts.** `FABL.DNFTerm.mem_support_of_mem_literals`, `FABL.DNFTerm.positionOfSupport_index`.
