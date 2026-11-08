<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Segment.zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-step computation segment

**Claim.** If $P$ holds for the work-tape head positions of $a$, then the zero-step run from $a$ to itself is a segment of length zero.

**Proof.** The endpoint equation holds because zero iterations leave the configuration unchanged. There are no natural times strictly before $0$, so the avoidance condition has no instances. The only time at most $0$ is time $0$, when the configuration is $a$ and the position condition is the hypothesis.
