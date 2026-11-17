<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterLoopTMVia_escape_witness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Loop Escape Witness

**Claim.** If every round through $r_0$ satisfies the stated conditions and the next round configuration is in state $ex$, then the counter-loop machine reaches its escape configuration after the sum of those round lengths and the counter overhead. Before the endpoint it is never halting, done, or escape; through the endpoint its extra head stays in the specified interval and its first $k$ head positions match a corresponding run of $M$.

**Proof.** For each round, use the cut property (`Turing.Round.cut_some`) to show that every positive intermediate state is live, differs from $a$, and is not $ex$: membership outside the round’s exit set $\{some\ ex\}$ gives the last assertion. Thus the round hypotheses have the form required by `Turing.counterLoopTMVia_run_escape`. That theorem supplies the exact escape endpoint, the counter tape contents, the pre-endpoint exclusions, and both head-position bounds and tracking witnesses. The endpoint configuration is live, so `Turing.Segment.live` adds halting to the forbidden states before the endpoint. Unpacking the resulting segment gives the asserted witness.

**Key facts.** `Turing.Round.cut_some`, `Turing.counterLoopTMVia_run_escape`, `Turing.Segment.live`.
