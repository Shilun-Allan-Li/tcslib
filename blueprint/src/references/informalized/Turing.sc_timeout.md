<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_timeout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded timeout of a clocked simulation

**Claim.** If the body machine is not stopped through the time represented by the initial counter word, the clocked machine reaches a timeout configuration carrying the body machine's configuration at that deadline, within the stated step bound. Before that endpoint it is in neither exit family, and throughout the run its body data matches some configuration reached by the body machine by the deadline while the clock head stays in the specified interval.

**Proof.** Write $d$ for the value represented by the Boolean word $w$. The round theorem, applied with $n=d$, reaches the body configuration at time $d$ after the round overhead plus $d$ steps, with the counter word for round $d$; it also supplies the segment and intermediate-time trace (`sc_rounds`). The body machine is still live at time $d$, so choose its state $s$ with $\mathrm{stopAt}(s)=\mathrm{false}$ (`sc_live`). The counter word at this point represents zero: the value identity for counter words gives value $d-d=0$ (`counterWord_value`), and zero value is equivalent to the fixed decrement being exhausted (`counter_dec_zero`).

One final debit therefore takes the exhausted-counter branch. The debit lemma supplies a segment with the clock head in range and a trace through that final phase (`sc_clockDebit`). The updated counter has the same length as the initial one (`counterWord_length`), so replacing the prior patch by the final patch is valid (`sc_wordPatch_twice`). Concatenating the round segment and this debit segment gives the full segment (`Segment.trans`), and the delivery lemma packages the endpoint, the absence of earlier exits, and the body-data trace (`sc_deliver`).

For the time bound, the overhead recurrence expresses the last round's debit cost as the final summand. The amortized bound on total counter overhead then yields the claimed upper bound after adding the $d$ body steps and simplifying (`counterOverhead_succ`, `counterOverhead_le`). The final counter word has the same length as $w$, so it supplies the required word $w'$ and length equality (`counterWord_length`).

**Key facts.** `Turing.sc_rounds`, `Turing.sc_live`, `Turing.counterWord_value`, `Turing.counter_dec_zero`, `Turing.sc_clockDebit`, `Turing.counterWord_length`, `Turing.sc_wordPatch_twice`, `Turing.Segment.trans`, `Turing.sc_deliver`, `Turing.counterOverhead_succ`, `Turing.counterOverhead_le`.
