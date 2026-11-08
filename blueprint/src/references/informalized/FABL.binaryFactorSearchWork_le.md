<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryFactorSearchWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Factor Search Work Bound

**Claim.** For every natural number $\ell$, the work required by the binary factor search is at most $8(\ell+1)^2 2^{2\ell}$.

**Proof.** By the exact factor-search work formula (`binaryFactorSearchWork_eq`), the work is $2^{2\ell}$ times the binary product comparison work plus $4$. The comparison work is at most $4(\ell+1)^2$ (`binaryProductComparisonWork_le`). Since $(\ell+1)^2\ge1$, the added $4$ is at most $4(\ell+1)^2$, so the parenthesized cost is at most $8(\ell+1)^2$. Multiplying by $2^{2\ell}$ preserves the inequality, and rearranging the factors gives the stated bound.

**Key facts.** `FABL.binaryFactorSearchWork_eq`, `FABL.binaryProductComparisonWork_le`.
