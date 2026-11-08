<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/ClockMachine.lean :: Complexity.TimeHierarchy.ctrPop_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True Bits in a Repeated Prefix

**Claim.** The number of true entries in $j$ copies of $b$ followed by $r$ is $(j$ if $b$ is true, and $0$ otherwise$)$ plus the number of true entries in $r$.

**Proof.** Induct on $j$. When $j=0$, the repeated prefix is empty, so the count is just that of $r$. For the inductive step, prepend one more copy of $b$. If $b$ is false it adds no true entries; if $b$ is true it adds exactly one. In either case the count increases by precisely the contribution of this extra copy, giving the stated formula from the induction hypothesis.
