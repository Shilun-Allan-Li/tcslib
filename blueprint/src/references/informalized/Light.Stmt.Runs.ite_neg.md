<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Stmt.Runs.ite_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# False branch of a conditional run

**Claim.** If the false branch $t$ runs safely from $\sigma$ to $R$, and the condition is safe there and false there, then the conditional with branches $s,t$ runs safely from that state to $R$.

**Proof.** The conditional is block-safe because its condition is safe, its true-branch obligation follows vacuously from the condition being false, and its false-branch obligation is exactly the block-safety part of the assumed run of $t$. Since the condition is false, the conditional's resulting state is the state resulting from $t$. Thus the postcondition follows from the assumed postcondition for $t$.
