<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.two_pow_le_mul_primeCounting -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prime counting lower bound

**Claim.** For every natural number $L\ge1$, $2^L\le L\bigl(\operatorname{primeCounting}(2^L)+1\bigr)$.

**Proof.** Write $L=k+1$, which is possible because $L\ge1$. Apply the bound $4^n\le(2n)^{\operatorname{primeCounting}(2n)+1}$ with $n=2^k>0$ ($\texttt{four_pow_le_pow_primeCounting}$). Here $2n=2^{k+1}=2^L$, and $4^n=2^{2n}$. Thus $2^{2^L}\le(2^L)^{\operatorname{primeCounting}(2^L)+1}$. Since the base $2$ is greater than $1$, comparing exponents yields $2^L\le L(\operatorname{primeCounting}(2^L)+1)$, as required.

**Key facts.** `Randomized.four_pow_le_pow_primeCounting`.
