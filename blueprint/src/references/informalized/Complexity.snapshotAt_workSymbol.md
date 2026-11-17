<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Snapshot.lean :: Complexity.snapshotAt_workSymbol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Symbol from the Last Visit

**Claim.** The symbol under a work-tape head at time $t$ is blank if its current scheduled position was never visited earlier; otherwise it is the symbol left by the step at the greatest earlier visit to that position, with a halted machine or a transition making no write preserving the previously scanned symbol.

**Proof.** Obliviousness identifies the work-head position on input $x$ at every time with the position scheduled on the all-zero input of the same length. Thus it suffices to track the cell at the time-$t$ scheduled position. If there is no earlier visit, the no-visit characterization of the previous-visit search says the head avoids this cell at every time before $t$. The cell-invariance lemma then transports its initial blank content unchanged to time $t$. If the previous-visit search returns $s$, its last-visit characterization gives $s<t$, equality of the head position at times $s$ and $t$, and no visits to that position strictly between them. Apply cell invariance from time $s+1$ through time $t$ to see that the content at time $t$ equals its content just after step $s$. The one-step cell update says that this content is the transition's written-or-kept symbol exactly when the head at time $s$ is at that cell. The scheduled-position equality and the visit condition establish this, yielding the stated result.

**Key facts.** `Complexity.oblivious_schedule_eq`, `Complexity.prevVisit_none_no_visit`, `Complexity.workCell_eq_of_no_visit`, `Complexity.prevVisit_some_last`, `Complexity.workCell_succ`.
