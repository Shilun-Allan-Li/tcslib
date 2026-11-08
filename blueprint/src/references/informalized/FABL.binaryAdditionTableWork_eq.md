<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryAdditionTableWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Addition Table Work

**Claim.** For every natural number $\ell$, the work assigned to the full binary addition table on vectors of length $\ell$ is $2^{2\ell}(\ell+1)$.

**Proof.** The table-work formula (`FABL.binaryOperationTableWork_eq`) states that a table on length-$\ell$ vectors, with operation cost $w$, has work $2^{2\ell}(w+1)$. Binary addition has cost $\ell$ by `FABL.binaryAddWork_eq`. Substituting $w=\ell$ gives the claimed value.

**Key facts.** `FABL.binaryAddWork_eq`, `FABL.binaryOperationTableWork_eq`.
