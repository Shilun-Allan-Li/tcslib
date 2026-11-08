<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_deliver -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Delivery by the clocked machine

**Claim.** Under the stated endpoint, bounded-time, exit, segment, and trace hypotheses, there is a time at most $B$ and a Boolean word of width $|w|$ for which the clocked machine reaches the corresponding patched configuration, avoids finish and timeout states at all earlier times, and keeps its original work tapes, input position, output, and counter-head bound synchronized with some run of $M$ through that time.

**Proof.** Choose the supplied time $T$ and word $w'$. The time bound, width, and endpoint requirements are exactly the corresponding hypotheses. Since the endpoint state belongs to the finish-or-timeout exit set, the first-exit consequence of the segment hypothesis (`sc_firstExit`) shows that no earlier state lies in that exit set. Unpacking membership in this set gives avoidance of both finish and timeout states. For any time through $T$, take the configuration and body-run time supplied by the trace hypothesis. The trace identifies the clocked configuration as a clock configuration over that body run; reading its original tapes, input position, and output therefore gives the asserted equalities, and its head bound is the trace's bound.

**Key facts.** `Turing.sc_firstExit`.
