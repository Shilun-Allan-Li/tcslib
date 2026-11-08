<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Round.iterate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Successive Rounds

**Claim.** Under the stated round hypotheses, the run over the sum of the $n$ durations ends at $c_n$, avoids $E$ at every time before the endpoint, and satisfies $P$ throughout the run, including its endpoints.

**Proof.** Proceed by induction on $n$. For $n=0$, the orbit endpoint is the starting configuration and the total duration is zero; the zero-length segment property (`Turing.Segment.zero`) follows from the assumed property $P$ at the start. For the successor case, the induction hypothesis concatenates the first $n$ rounds into a segment from $c$ to the $n$th orbit configuration. The next round, together with the assumption that $\mathrm{some}(a)\notin E$, gives a segment over its duration (`Turing.Round.segment`). Concatenating these two segments with the segment composition property (`Turing.Segment.trans`) gives a segment to the next orbit configuration, with duration the previous sum plus the new round duration. The finite sum over $n+1$ rounds is precisely this sum, completing the induction.

**Key facts.** `Turing.Segment.zero`, `Turing.Round.segment`, `Turing.Segment.trans`.
