<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.fanoutIn_sealTriple -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-out in a three-gate construction

**Claim.** For the three gates reading $u$, $(u,N)$, and $(o,N+1)$, the fan-out of $v$ is $2$ when $v=u$, plus $1$ when $v=N$, plus $1$ when $v=o$, plus $1$ when $v=N+1$, with each term zero unless its stated equality holds.

**Proof.** Count the three gates separately. The NOT gate reads only $u$, so it contributes one exactly when $v=u$. The OR gate reads $u$ and $N$, contributing one when either of those equals $v$. The AND gate reads $o$ and $N+1$, contributing one when either equals $v$. The conditions $u<N$ and $o<N$ ensure that the two arguments within each of the latter gates are distinct; also $N$ and $N+1$ are distinct. The only possible overlap in the contributions across gates is at $u$, which is read by both the NOT and OR gates, yielding the coefficient two. Summing these indicators gives the displayed formula.
