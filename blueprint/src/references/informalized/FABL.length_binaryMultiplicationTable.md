<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.length_binaryMultiplicationTable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary multiplication table size

**Claim.** For positive $[?]ell$, the binary multiplication table has length $2^{2\ell}$.

**Proof.** The table is formed by applying the multiplication operation to every ordered pair from the list of all binary vectors of length $\ell$. The length of a binary operation table is the square of the length of its input list (\texttt{length_binaryOperationTable}). Since the list of all binary vectors has length $2^\ell$ (\texttt{length_allBinaryVectors}), the table has length $(2^\ell)^2$. The exponent law gives $(2^\ell)^2=2^{\ell+\ell}=2^{2\ell}$.

**Key facts.** `FABL.length_binaryOperationTable`, `FABL.length_allBinaryVectors`.
