<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryProductComparisonWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Comparison Work Formula

**Claim.** For every natural number $\ell$, the product comparison work is $(2\ell+1)(2\ell+2)$.

**Proof.** The traversal work equals the list length times its per-step cost ($\texttt{binaryConstructorTraversalWork_eq}$). Here the list is the range of length $2\ell+1$, and each step costs $2\ell+2$. Their product is the stated formula.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`.
