<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRow_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Return at the End of a Row

**Claim.** For a positive number of fields, the row machine reaches the end-of-row state in copier start control within $l(3W+4)$ steps, with the input position, counter words, and heads unchanged and the record extended by the packed full row; it does not reach that state at any earlier time.

**Proof.** The stored-row result (`clRow_stored`) gives a time $B\le l(3W+4)$ at which the machine is at the end-of-row state with copier control $0$, and the record contains the packed full row. Among all times at most $B$ when the machine is in that state, choose the least, say $t$. The initial state has field index $0$, whereas the end-of-row index is $l>0$, so $t$ cannot be zero. By minimality, the machine has not reached the specified state at any earlier time. At that state the controller is idle: `clRow_idle` says its next step fixes the entire configuration. Consequently, once the machine reaches it at time $t$, it stays there through time $B$. The configuration at time $B$, supplied by `clRow_stored`, therefore also describes the configuration at time $t$. The bound on $t$ follows from $t\le B$.

**Key facts.** `Complexity.clRow_stored`, `Complexity.clRow_idle`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_add`.
