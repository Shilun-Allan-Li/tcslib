<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean :: Complexity.TQBFHard.wP_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Length Bound

**Claim.** For every natural number $n$, the length of the binary representation of $n+1$ is at most $n+1$.

**Proof.** Apply the general bound that if $m<2^r$, then the binary representation of $m$ has length at most $r$ (Complexity.LogProg.length_bits_le). Take $m=n+1$ and $r=n+1$; the strict inequality $n+1<2^{n+1}$ follows from the standard bound $k<2^k$ for positive $k$, here with $k=n+1$. This yields the claimed estimate.

**Key facts.** `Complexity.LogProg.length_bits_le`.
