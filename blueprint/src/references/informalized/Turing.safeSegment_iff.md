<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.safeSegment_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safe Segment Characterization

**Claim.** A safe computation segment from $a$ to $b$ in time $t$ is equivalent to reaching $b$ at time $t$, having state outside $F$ at every time from $0$ through $t$, and satisfying $P$ for the work-head positions at every such time.

**Proof.** Unpacking safety gives the endpoint equation, the state avoidance condition for times $u<t$, the head-position condition for times $u\le t$, and the additional requirement that the endpoint state $b$ lies outside $F$. To extend state avoidance to all $u\le t$, split into $u<t$, where the segment condition applies, and $u=t$, where the endpoint equation identifies the run state with $b$ and the endpoint requirement applies. Conversely, if state avoidance and the head-position condition hold through time $t$, their restrictions give the segment conditions: in particular, $u<t$ implies $u\le t$. Taking $u=t$ in state avoidance and using the endpoint equation shows that $b$ lies outside $F$, recovering safety.
