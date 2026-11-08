<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryFactorSearchWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Factor Search Work

**Claim.** For every natural number $\ell$, the work assigned to the binary factor search is $2^{2\ell}$ times the sum of the binary product comparison work at length $\ell$ and $4$.

**Proof.** Each item in the traversal incurs the same step cost, namely the binary product comparison work plus $4$. The traversal work therefore equals the number of items times that cost (the constant-cost traversal formula, `binaryConstructorTraversalWork_eq`). The items are all ordered pairs of binary vectors of length $\ell$, and their list has length $2^{2\ell}$ (`length_binaryVectorPairs`). Substituting this length into the traversal formula gives the claimed product.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`, `FABL.length_binaryVectorPairs`.
