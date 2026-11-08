<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterLoopTMVia_done_segment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Loop Completion Segment

**Claim.** Under the round, counter-encoding, and head-position hypotheses, the counter-loop machine reaches the specified done configuration after the sum of the body-run times and the counter overhead; before then it avoids done and escape, and the extra head and first $k$ heads satisfy the stated position property throughout.

**Proof.** Begin with the stronger completion-segment witness, which supplies the endpoint, the exact elapsed time, absence of the states done, escape, and halting before that time, and the position invariant at every time through the endpoint (Turing.counterLoopTMVia_done_witness). The desired segment excludes halting from its forbidden set, so its forbidden set is a subset of the witness's forbidden set. It remains to retain the first-$k$-head part of the invariant. At an arbitrary time covered by the witness, its decomposition places the run either within round $r<d$ or at a round boundary. Within a round, the round hypothesis asserts that $P$ holds at every time up to that round's endpoint. At a boundary after a positive number of rounds, the preceding round's endpoint condition gives $P$; at the initial boundary, $P$ is the assumption on $c$. Thus $P$ holds at the first $k$ head positions throughout. Combining this with the witness's bound on the extra head gives the required invariant, and segment monotonicity transfers the witness to the smaller forbidden set and this invariant (Turing.Segment.mono).

**Key facts.** `Turing.counterLoopTMVia_done_witness`, `Turing.Segment.mono`.
