<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterLoopTMVia_escape_segment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Loop Escape Segment

**Claim.** Under the stated hypotheses, the counter-loop machine reaches its escape configuration with the extra tape containing the encoded counter word after $r_0+1$ decrements. Before the endpoint it is neither done nor escape; throughout the segment the extra head stays in the stated interval and property $P$ holds for the first $k$ head positions.

**Proof.** Apply the escape witness theorem (`Turing.counterLoopTMVia_escape_witness`) to obtain a segment that also excludes halting before the endpoint and records, at every time, the extra-head interval together with a witness identifying the corresponding run of $M$. The required segment forbids only done and escape, so its forbidden-state set is a subset of the witness theorem’s set; this is the state-set part of `Turing.Segment.mono`. For the property component, take the witness indices $r,u$. If $r\le r_0$, the round hypothesis gives $P$ at time $u$, since $u$ is at most that round’s length. In the endpoint case $r=r_0+1$ and $u=0$, use the final round’s endpoint property, then identify its endpoint configuration with the start configuration of round $r_0+1$. The witness equality identifies the first $k$ head positions with those of this run, so $P$ transfers to them. A final application of `Turing.Segment.mono` yields the stated segment.

**Key facts.** `Turing.counterLoopTMVia_escape_witness`, `Turing.Segment.mono`.
