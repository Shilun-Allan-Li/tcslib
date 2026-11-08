<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityBlockSide_le_root_add_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity block side bound

**Claim.** For natural numbers $n$ and $h$, if $R=n^{1/h}$ and $B$ is the maximum of $1$ and the least natural number at least $R$, then $B\le R+1$.

**Proof.** The root $R$ is nonnegative, so $1\le R+1$. Also, the ceiling property for a nonnegative real gives $\lceil R\rceil\le R+1$. Since both entries in the maximum defining $B$ are at most $R+1$, their maximum is as well.

**Key facts.** `FABL.parityRealRoot_nonneg`.
