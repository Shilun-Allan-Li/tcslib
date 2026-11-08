<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_observedSegment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Observed Run Forms a Segment

**Claim.** If the run avoids a specified set of states at every time before $t$ and satisfies a head-position property through time $t$, then it forms a segment ending at its time-$t$ configuration with those same properties.

**Proof.** Proceed by induction on $t$, generalizing the starting configuration. At time zero, the run ends where it starts, and the head-position hypothesis at time zero gives the required property; this is the zero-length segment (`Segment.zero`). For the successor case, regard the first step as leading to the new starting configuration. The run-from-successor identity (`MultiTapeTM.runFrom_succ_eq_step`) transfers both hypotheses to that configuration: a time $u$ in its run corresponds to time $u+1$ in the original run. The induction hypothesis gives a segment for the remaining $t$ steps. Prepend the first step using the segment concatenation result (`Segment.cons`): the original state at time zero avoids the exit set, the head-position property holds there, and the tail segment supplies the corresponding facts thereafter. The run-from-successor identity identifies the concatenated endpoint with the original run at time $t+1$.

**Key facts.** `Turing.Segment.zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.Segment.cons`.
