<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.p2_marks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Leftward Sweep Marks

**Claim.** For a choice word $w$ of length at most $m$, starting phase $p2$ with yard head at $|w|-1$ and running under $w$ leaves phase $p2$, advances each work-tape head of $A$ by $|w|$, and ends with yard head at $-1$, preserving the other tapes and output.

**Proof.** Induct on the word $w$. For the empty word, running makes no step, and the starting yard-head position is $-1$; the claimed head displacement is zero. For $w=b::v$, the length bound gives $|v|+1\le m$. The yard has a true mark at position $|v|$, since this position is nonnegative and strictly less than $m$ (`yard_of_lt`). The run on the cons word first performs the step for $b$ and then runs on $v$ (`runWith_cons`). The one-step marked-cell result (`p2_mark`) keeps phase $p2$, advances each of $A$'s heads by one, and moves the yard head from $|v|$ to $|v|-1$. This is the required starting position for the induction hypothesis on $v$. Applying that hypothesis gives total head displacement $1+|v|=|w|$ and final yard position $-1$; the tapes and output remain unchanged throughout.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.ClockHost.yard_of_lt`, `Turing.ClockHost.p2_mark`.
