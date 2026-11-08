<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterLoopTMVia_done_witness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Loop Completion Witness

**Claim.** Under the stated round hypotheses and initial buffer agreement, the counter-loop machine reaches its done configuration after the sum of the round lengths plus the counter overhead. The counter tape contains true symbols across the word, the extra head stays within the stated interval, and the first $k$ head positions track a corresponding run of $M$; before the endpoint the state is never halting, done, or escape.

**Proof.** First, each round hypothesis supplies a positive run length, a start in state $a$, and a return to state $a$. The round cut property (`Turing.Round.cut_some`) further says that at every positive intermediate time the machine is in a live state different from $a$ and outside the designated exit set. These facts put the hypotheses into the form required by the counter-loop completion theorem. Applying `Turing.counterLoopTMVia_run_done` gives the exact endpoint configuration and time, the exclusion of done and escape before that time, and the extra-head interval and first-$k$-head tracking properties through the endpoint. Its endpoint configuration has no halting state, so `Turing.Segment.live` strengthens the segment’s forbidden-state set to include halting as well. The desired witness follows by unpacking the segment property.

**Key facts.** `Turing.Round.cut_some`, `Turing.counterLoopTMVia_run_done`, `Turing.Segment.live`.
