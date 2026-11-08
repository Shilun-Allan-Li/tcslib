<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHard.lean :: Complexity.TQBFHard.time_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reduction time bound

**Claim.** If $\sigma$ has the prescribed output width at input length $|x|$, then the stated polynomial bound in the length of the paired encoding of $x$ and $\sigma$ is at most the reduction time bound.

**Proof.** Put $n=|x|$, $A=wCoef$, and $P=(n+1)^{c+1}$. Since $n+1\ge1$, we have $1\le P$ and $n+1\le P$, hence $P\le P^2$. The pairing-length formula (Turing.length_pairEncode) and the assumed length of $\sigma$ show that $|\langle x,\sigma\rangle|+1$ is at most $redK\,(n+1)^{2(c+1)}$: after rewriting the power as $P^2$, the width contribution is $3A^2P^2+3AP$, which is bounded by the corresponding terms in $redK P^2$, and the remaining $2n+3$ is bounded by $3P^2$. Raise this inequality to the power $c_V$ and multiply by $CV$. The power laws combine the factors into $CV\,redK^{c_V}(n+1)^{2(c+1)c_V}$, which is at most the reduction time bound because that bound adds one.

**Key facts.** `Turing.length_pairEncode`.
