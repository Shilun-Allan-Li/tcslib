<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.SafeSegment.zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safe Segment of Length Zero

**Claim.** If $a$'s state is outside $F$ and $P$ holds at its work-tape head-position vector, then there is a safe segment from $a$ to itself of length zero.

**Proof.** The zero-length segment result gives a segment from $a$ to itself: its run endpoint is $a$, there are no times before zero to check for forbidden states, and the position condition at time zero is precisely the assumed predicate `Turing.Segment.zero`. The separate hypothesis that $a$'s state is outside $F$ supplies the safe-segment endpoint condition.

**Key facts.** `Turing.Segment.zero`.
