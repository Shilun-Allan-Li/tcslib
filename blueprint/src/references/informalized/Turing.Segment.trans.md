<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Segment.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation of computation segments

**Claim.** Two consecutive segments, from $a$ to $b$ in $t$ steps and from $b$ to $c$ in $v$ steps, concatenate to a segment from $a$ to $c$ in $t+v$ steps, provided both satisfy the same avoidance and position conditions.

**Proof.** The endpoint after $t+v$ steps is $c$: split the run at time $t$ using the run composition law ($\texttt{Turing.MultiTapeTM.runFrom_add}$), then use the first segment's endpoint equation to identify the intermediate configuration with $b$, and the second segment's endpoint equation to identify the result with $c$. For any time $u<t+v$, split into two cases. If $u<t$, the first segment supplies avoidance of $F$. Otherwise write $u=t+(u-t)$; then $u-t<v$, and run composition together with the first endpoint equation identifies the configuration at time $u$ with the second run at time $u-t$, where avoidance follows from the second segment. For the position condition at any $u\le t+v$, if $u\le t$ the first segment supplies it. If $u>t$, write $u=t+(u-t)$; now $u-t\le v$, so run composition and the first endpoint equation reduce the claim to the second segment's position condition.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
