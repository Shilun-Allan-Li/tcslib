<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCopy_first -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Positive Copier Completion

**Claim.** For every input word, valid input-head position, source word, and record, there is a positive time at most three times the source length plus three at which the copier reaches the completed control and the specified final configuration; at every earlier time it is not in that control.

**Proof.** The exact-run result (`clCopy_run`) supplies a time $N=3|w|+3$ at which the copier is in the completed control. Choose the least time $t$ no greater than $N$ at which that control is reached. This time is positive: at time zero the initial control is state $0$, not state $4$. By minimality, no time $j<t$ can have state $4$. Finally, the completed control is absorbing (`clCopy_idle`), so once reached the configuration stays fixed for the remaining $N-t$ steps. The configuration at time $t$ therefore equals the exact-run configuration at time $N$, which is the required one.

**Key facts.** `Complexity.clCopy_run`, `Turing.MultiTapeTM.runFrom_zero`, `Complexity.clCopy_idle`, `Turing.MultiTapeTM.runFrom_add`.
