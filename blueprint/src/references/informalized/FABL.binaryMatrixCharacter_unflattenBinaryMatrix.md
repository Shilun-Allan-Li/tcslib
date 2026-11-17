<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.binaryMatrixCharacter_unflattenBinaryMatrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matrix Character Under Unflattening

**Claim.** Evaluating the matrix character of $A$ at the matrix obtained by unflattening $x$ gives the dot product of the flattening of $A$ with $x$.

**Proof.** The character is the matrix pairing of $A$ with the unflattening of $x$. By the flattening-pairing identity ($\texttt{f₂DotProduct_flattenBinaryMatrix}$), this pairing equals the dot product of the flattened matrices $A$ and the unflattened matrix. Flattening the unflattening recovers $x$, since the indexing equivalence between pairs of indices and indices of length $n^2$ is inverse to itself. Substituting this recovery gives the stated dot product.

**Key facts.** `FABL.f₂DotProduct_flattenBinaryMatrix`.
