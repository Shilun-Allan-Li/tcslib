<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryXMulModWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary multiplication work

**Claim.** For every natural number $\ell$, the work required by the binary multiplication procedure is exactly $4\ell+1$.

**Proof.** The traversal over the list of the first $\ell$ natural numbers costs the list length times the per-item cost, by the traversal formula `binaryConstructorTraversalWork_eq`. The list has length $\ell$, and each item costs $4$, so the traversal costs $4\ell$. The procedure adds one final unit of work, giving $4\ell+1$.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`.
