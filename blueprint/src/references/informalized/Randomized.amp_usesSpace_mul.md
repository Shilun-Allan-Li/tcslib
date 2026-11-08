<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.amp_usesSpace_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space bound for the amplified machine

**Claim.** If every run of $N$ uses at most $s(n)$ space on inputs of length $n$, then the amplified machine using $r$ has space at most $3(r+1)k_Ns(n)$ for every input of length $n$, for any decision function on the run count.

**Proof.** The amplification space estimate (`Randomized.Amplify.amp_usesSpace`) bounds the space by $(r+1)k_N(2s(n)+1)$. If $k_N=0$, this bound and the desired bound are both zero. Otherwise, the original space bound implies $k_N\le s(n)$ (`Turing.FinNDTM.UsesSpace.k_le`), so in particular $s(n)\ge1$. Hence $2s(n)+1\le3s(n)$, and multiplying by $(r+1)k_N$ gives the claimed estimate. The monotonicity of the space-use predicate then promotes the pointwise estimate to the stated bound (`Turing.FinNDTM.UsesSpace.mono`).

**Key facts.** `Randomized.Amplify.amp_usesSpace`, `Turing.FinNDTM.UsesSpace.k_le`, `Turing.FinNDTM.UsesSpace.mono`.
