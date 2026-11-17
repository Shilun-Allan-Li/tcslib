<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Segment.drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffixes of computation segments

**Claim.** If a segment from $a$ to $b$ has length $t$, avoids $F$ before time $t$, and satisfies $P$ through time $t$, then after any $u\le t$ the remaining run from the configuration at time $u$ is a segment to $b$ of length $t-u$.

**Proof.** A segment consists of its endpoint equation, its avoidance condition, and its position condition. For the endpoint, the run of length $t-u$ starting at time $u$ is the original run through $u+(t-u)$ steps, by the composition law for runs ($\texttt{Turing.MultiTapeTM.runFrom_add}$). Since $u\le t$, this sum is $t$, so the result is $b$. For any time $v<t-u$ in the suffix, the corresponding original time is $u+v<t$; the original segment therefore says its state is outside $F$. Finally, if $v\le t-u$, then $u+v\le t$, so the original position condition gives $P$ at the corresponding configuration. The same run-composition law identifies that configuration with the suffix run at time $v$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
