<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Reductions.lean :: Randomized.polyLen_length_pairEncode_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Encoding Preserves Polynomial Length Bounds

**Claim.** Under the stated polynomial bound on $|f(z)|$ and the specified length of $r$, the polynomial bound for $|f(\langle x,r\rangle)|$ is at most the claimed polynomial in $|x|$.

**Proof.** Put $n=|x|$. Pair encoding has length $2n+2+|r|$. Since $|r|=a_1(n+1)^{k_1}$ and both $n+1$ and $(n+1)^{k_1}$ are bounded by $(n+1)^{k_1+1}$, this gives $|\langle x,r\rangle|+1\le(a_1+3)(n+1)^{k_1+1}$. Applying the assumed bound for $f$ and adding $1$, we obtain $|f(\langle x,r\rangle)|+1\le(C+1)(a_1+3)^c(n+1)^{(k_1+1)c}$: the added $1$ is absorbed because the encoded input length plus one is positive, so its $c$th power is at least $1$. Raising this inequality to the $k_2$th power and multiplying by $a_2$ gives the asserted bound; the coefficient and exponent combine to $a_2((C+1)(a_1+3)^c)^{k_2}$ and $(k_1+1)ck_2$, respectively.

**Key facts.** `Turing.length_pairEncode`.
