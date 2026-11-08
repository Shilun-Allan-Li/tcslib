<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_span_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Counter Spans

**Claim.** If a run has the stated span properties for an initial interval of length $s$ and its continuation has them for an interval of length $t$, and each interval's work-head invariant implies a common invariant, then the full run has those properties for length $s+t$.

**Proof.** Consider any time $u$ in the combined interval. If $u<s$, it lies in the first span, so that span gives avoidance of both exit anchors, the counter-head bound, and its work-head invariant, which implies the common invariant. If $u\ge s$, the run at time $u$ is the run from its time-$s$ configuration for $u-s$ steps: the iteration law for runs gives this decomposition, since $s+(u-s)=u$. The suffix time lies in the second span's interval, so its avoidance and counter-head bound apply, and its work-head invariant implies the common one. For avoidance, the combined span only asks about times strictly before $s+t$; in the suffix case this makes $u-s<t$. For the position and invariant bounds, $u\le s+t$ gives $u-s\le t$. These cases establish all three span conditions.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
