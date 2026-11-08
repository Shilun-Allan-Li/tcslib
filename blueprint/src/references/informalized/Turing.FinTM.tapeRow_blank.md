<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.tapeRow_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank unread block

**Claim.** If no work-tape head is at coordinate $j$ and every work tape is blank there, then the unread block encoding that coordinate is the blank block with its mark cleared.

**Proof.** Both rows are mapped over the same list of work-tape indices. Fix any such index $i$. The assumption that the tape is blank at $j$ makes its symbol component `none`. The head condition makes the current-head mark false; because the read flag is false, the final component is also false. Thus the entries agree at every index, and hence the two mapped lists are equal.
