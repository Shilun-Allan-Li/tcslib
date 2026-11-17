<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.executableSmallBiasPowerWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power work formula

**Claim.** For natural numbers $\ell$ and $e$, the assigned work for computing a power is $\ell+e\bigl(W(\ell)+1\bigr)$, where $W(\ell)$ is the binary modular multiplication work.

**Proof.** The traversal work on a list is its length times the per-item work (\texttt{FABL.binaryConstructorTraversalWork_eq}). The list of exponents from $0$ to $e-1$ has length $e$. Substituting these into the definition of power work gives $\ell+e\bigl(W(\ell)+1\bigr)$.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`.
