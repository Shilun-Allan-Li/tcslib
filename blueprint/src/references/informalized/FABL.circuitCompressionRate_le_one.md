<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.circuitCompressionRate_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compression Rate Bound

**Claim.** For positive natural numbers $w$ and $\ell$, the circuit compression rate is at most $1$.

**Proof.** The rate is the product of the switching-layer rate at $w$ and the $r$th power of the switching-layer rate at $\ell$. The first factor is at most $1$ by the switching-layer rate bound (`FABL.switchingLayerRate_le_one`), and both factors are nonnegative by nonnegativity of that rate (`FABL.switchingLayerRate_nonneg`). Thus its $r$th power is nonnegative and at most $1$. The product of two nonnegative quantities each at most $1$ is at most $1$, giving the result.

**Key facts.** `FABL.switchingLayerRate_le_one`, `FABL.switchingLayerRate_nonneg`.
