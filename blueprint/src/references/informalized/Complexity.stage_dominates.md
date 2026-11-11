<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.stage_dominates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stage time bound dominates

**Claim.** If $c,k,i$ are nonnegative integers with $k+1+2c\le i$, then $c(n_i^k+1)\le n_i^i+i$, where $n_i$ is the fresh length chosen at stage $i$.

**Proof.** Write $n=n_i$. The fresh-length property gives $i+2\le n$, so the hypothesis implies $2c\le n$. Also $1\le n^k$, hence $n^k+1\le2n^k$. Therefore
\[c(n^k+1)\le 2c n^k\le n\,n^k=n^{k+1}\le n^i\le n^i+i.\]
The penultimate inequality follows from $k+1\le i$ and monotonicity of powers with base at least one; the last follows because $i$ is nonnegative.

**Key facts.** `Complexity.freshLen_spec`.
