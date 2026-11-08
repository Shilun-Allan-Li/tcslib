<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Segment.take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial segments of computation

**Claim.** For any $u\le t$, a segment from $a$ to $b$ of length $t$ yields a segment from $a$ to its time-$u$ configuration of length $u$, with the same avoidance and position conditions restricted to those times.

**Proof.** The endpoint of the proposed initial segment is defined as the configuration reached after $u$ steps, so its endpoint equation is immediate. Every time $v<u$ is also before the original endpoint time $t$, and thus the original segment gives avoidance of $F$ at time $v$. Likewise, every $v\le u$ is at most $t$, so the original position condition gives $P$ at time $v$.
