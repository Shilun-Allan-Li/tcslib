<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.length_binaryAdditionTable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the binary addition table

**Claim.** For every nonnegative integer $\ell$, the list of triples formed from all ordered pairs of binary vectors of length $\ell$ and their sums has length $2^{2\ell}$.

**Proof.** The table construction lists one triple for each ordered pair of entries in the vector list. Its length is therefore the square of the vector-list length, by the length formula for a binary operation table (`length_binaryOperationTable`). The vector list has length $2^\ell$ (`length_allBinaryVectors`), so the table length is $2^\ell\cdot2^\ell=2^{\ell+\ell}=2^{2\ell}$.

**Key facts.** `FABL.length_binaryOperationTable`, `FABL.length_allBinaryVectors`.
