<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.rew2_marks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the Yard Tape

**Claim.** Starting phase $rew2$ at yard position $|w|-1$, where $|w|\le m$, and running on $w$ leaves phase $rew2$ and all work tapes and output unchanged, moves the input head left $|w|$ times with clamping, and leaves the yard head at $-1$.

**Proof.** Induct on $w$. The empty word performs no steps, and both the input-head displacement and yard movement are zero. For a nonempty word $b::v$, the bound gives $|v|+1\le m$, so the yard cell at $|v|$ is marked: it is nonnegative and less than $m$ (`yard_of_lt`). Decompose the run into the first step on $b$ followed by the run on $v$ (`runWith_cons`). The marked-cell rewind step keeps phase $rew2$, moves the input head left once, and moves the yard head from $|v|$ to $|v|-1$ (`rew2_step`). That new position is the starting position required by the induction hypothesis. The induction result supplies the remaining $|v|$ left moves and ends at yard position $-1$; since each step leaves the work tapes and output alone, these remain unchanged.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.ClockHost.yard_of_lt`, `Turing.ClockHost.rew2_step`.
