<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryAddWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Addition Work

**Claim.** For every natural number $\ell$, the work assigned to binary addition on vectors of length $\ell$ is $\ell$.

**Proof.** The traversal-work formula (`FABL.binaryConstructorTraversalWork_eq`) says that traversing a list charges the step work once per item, so the total is the list length times the step work. Here the list is the range from $0$ to $\ell-1$, which has length $\ell$, and the step work is $1$. Therefore the total work is $\ell\cdot 1=\ell$.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`.
