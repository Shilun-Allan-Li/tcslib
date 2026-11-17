<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Stmt.Runs.ite_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True branch of a conditional run

**Claim.** If the true branch $s$ runs safely from $\sigma$ to $R$, and the condition is safe and true there, then the conditional with branches $s,t$ runs safely from that state to $R$.

**Proof.** The conditional is block-safe because its condition is safe, its true-branch obligation is the block-safety part of the assumed run of $s$, and its false-branch obligation follows vacuously from the condition being true. In this case the conditional's resulting state is the state resulting from $s$, so the assumed postcondition for $s$ gives the required postcondition.
