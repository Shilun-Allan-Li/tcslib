<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryAdditionTableWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Binary Addition Table Work

**Claim.** For every natural number $\ell$, the work assigned to the full binary addition table on vectors of length $\ell$ is at most $(\ell+1)^2 2^{2\ell}$.

**Proof.** The exact table-work formula (`FABL.binaryAdditionTableWork_eq`) gives $2^{2\ell}(\ell+1)$. Since $\ell+1\ge 1$, we have $\ell+1\le(\ell+1)^2$. Multiplying this inequality by the nonnegative number $2^{2\ell}$ and rearranging the factors yields the stated upper bound.

**Key facts.** `FABL.binaryAdditionTableWork_eq`.
