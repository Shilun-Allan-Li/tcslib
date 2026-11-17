<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.one_sub_one_sub_two_mul_pow_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of a power complement

**Claim.** If $0\leq\delta\leq\tfrac12$ and $m$ is a natural number, then $1-(1-2\delta)^m\ge0$.

**Proof.** The assumptions imply $0\le1-2\delta\le1$. A number in this interval has every natural power at most $1$, so $(1-2\delta)^m\le1$. Subtracting this inequality from $1$ gives the result.
