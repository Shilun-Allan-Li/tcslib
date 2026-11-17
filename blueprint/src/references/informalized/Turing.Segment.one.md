<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Segment.one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step computation segment

**Claim.** If the state of $a$ lies outside $F$, and $P$ holds for the work-tape positions of both $a$ and its one-step successor, then the run from $a$ to that successor is a segment of length one.

**Proof.** The endpoint equation holds because the endpoint is defined to be the one-step successor of $a$. The only natural time strictly before the endpoint time $1$ is time $0$, where the state lies outside $F$ by hypothesis. The times at most $1$ are exactly $0$ and $1$; at these times the position condition is precisely the two assumed instances of $P$.
