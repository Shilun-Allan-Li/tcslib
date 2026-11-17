<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.sc_firstExit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Earlier States Avoid the Exit Set

**Claim.** For a segment that avoids the exit set strictly before its endpoint and ends in that set, every state strictly before the endpoint lies outside the set.

**Proof.** Fix a time $u<t$. Restrict the given segment to its first $u$ steps using the segment restriction theorem (`Segment.take`); this gives a segment ending at the run's configuration at time $u$. The original segment ends in the exit set, and the restricted segment also ends there by the assumption that the earlier state lies in the set. The uniqueness-of-exit-time fact (`Segment.time_eq`) says these two segment lengths must agree. Thus $u=t$, contradicting $u<t$. Hence the state at time $u$ is outside the exit set.

**Key facts.** `Turing.Segment.take`, `Turing.Segment.time_eq`.
