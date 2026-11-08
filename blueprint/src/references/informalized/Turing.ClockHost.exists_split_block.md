<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.exists_split_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting a Boolean Word

**Claim.** If a Boolean word has length $m+1+r$, it can be written as a prefix of length $m$, followed by one Boolean, followed by a suffix of length $r$.

**Proof.** Consider the word obtained by dropping the first $m$ entries of $w$. It cannot be empty: if it were, the length formula for `drop` would give $|w|\le m$, contradicting $|w|=m+1+r$. Thus it has a first entry $b$ and a remaining suffix $v$. Take $u$ to be the first $m$ entries of $w$. The list decomposition into its first $m$ entries and the remainder gives $w=u++(b::v)$. The same length formulas show $|u|=m$ and, since $|w|=m+1+r$, $|v|=r$.
