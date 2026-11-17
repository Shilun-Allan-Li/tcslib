<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Snapshot.lean :: Complexity.workCell_eq_of_no_visit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unvisited Work Cells Retain Their Contents

**Claim.** If the work-tape head avoids cell $p$ at every time from $a$ through $b-1$, then that cell has the same contents after $a$ and $b$ steps.

**Proof.** Induct on $b$, allowing $a$ to vary. When $b=0$, the condition $a\le b$ forces $a=0$, so the two configurations agree. For the induction step, first suppose $a\le b$. The one-step work-cell update (`Complexity.workCell_succ`) says that at time $b+1$, cell $p$ contains the symbol written by the step if the head is at $p$ at time $b$, and otherwise keeps its time-$b$ content. The avoidance hypothesis excludes that head position. The contents at times $b+1$ and $b$ therefore agree, and the induction hypothesis applied to the interval from $a$ to $b$ shows that the contents at times $b$ and $a$ agree as well. In the remaining case, $a\nleq b$ while $a\leq b+1$, so $a=b+1$; the conclusion compares a configuration with itself.

**Key facts.** `Complexity.workCell_succ`.
