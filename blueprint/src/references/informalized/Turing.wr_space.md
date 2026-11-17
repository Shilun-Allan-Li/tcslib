<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.wr_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space bound from head displacement

**Claim.** If every work-tape head stays within distance $r$ of its initial position through time $t$, then the total number of distinct cells visited through that time is at most $k(2r+1)$.

**Proof.** Fix a tape. The displacement hypothesis places every head position from time $0$ through $t$ in the integer interval from its initial position minus $r$ to its initial position plus $r$. The visited-cell bound for an interval says that the number of visited positions is at most the number of integers in that interval ($\texttt{Turing.MultiTapeTM.spaceUsedByTape\_le\_card\_Icc}$), which here is $2r+1$. Sum this bound over the $k$ tapes. The sum has $k$ identical terms, giving $k(2r+1)$.

**Key facts.** `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc`.
