<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.executableVandermondeConstructionWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vandermonde construction work formula

**Claim.** For natural numbers $k$ and $n$, with $\ell=\max(1,\lceil\log_2 n\rceil)$, the executable Vandermonde construction work is the binary field preprocessing work at parameter $\ell$, plus $n$ times one more than the work for the first $k-1$ power rows at parameter $\ell$.

**Proof.** In the construction's work definition, the per-item cost is the work for the first $k-1$ power rows plus one, and the traversal runs over the list of the first $n$ natural numbers. Traversal work equals list length times per-item work (\texttt{FABL.binaryConstructorTraversalWork_eq}); that list has length $n$. Substitution yields the claimed formula, with the specified value of $\ell$.

**Key facts.** `FABL.binaryConstructorTraversalWork_eq`.
