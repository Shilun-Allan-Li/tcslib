<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityBlockSide_pow_covers -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity block side covers the input length

**Claim.** For natural numbers $n,h$ with $h>0$, if $s$ is the maximum of $1$ and the least natural number at least $n^{1/h}$, then $n\le s^h$.

**Proof.** Let $R=n^{1/h}$. For nonnegative $n$, the real power identity for the reciprocal of a positive natural exponent gives $R^h=n$. The ceiling, and hence its maximum with $1$, is at least $R$. Raising this inequality to the positive integer power $h$ preserves order because $R\ge0$. Thus $n=R^h\le s^h$ as real numbers, which yields the stated natural-number inequality.

**Key facts.** `FABL.parityRealRoot_le_blockSide`, `FABL.parityRealRoot_nonneg`.
