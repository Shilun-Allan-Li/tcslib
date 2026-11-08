<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryOperationTableWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Operation Table Work Formula

**Claim.** For every dimension $\ell$ and every operation with work cost $w$, the work to construct its table on pairs of binary vectors of length $\ell$ is $2^{2\ell}(w+1)$.

**Proof.** The traversal charges $w+1$ for each ordered pair in the table. Its total work is therefore the number of such pairs times $w+1$, by the traversal-work formula ($\texttt{binaryConstructorTraversalWork_eq}$). There are $2^{2\ell}$ ordered pairs of binary vectors of length $\ell$ ($\texttt{length_binaryVectorPairs}$), giving the result.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`, `FABL.length_binaryVectorPairs`.
