<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterOverhead_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive counter overhead

**Claim.** The overhead through round $r+1$ equals the overhead through round $r$ plus $2\ell_r+2$, where $\ell_r$ is the number of consecutive false bits at the beginning of the counter word after $r$ decrements.

**Proof.** By definition, the overhead is a sum over round indices. Splitting the sum over the first $r+1$ indices into the first $r$ terms and its final term gives the overhead through round $r$ plus the contribution of that round, namely $2\ell_r+2$.
