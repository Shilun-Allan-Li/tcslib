<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.executableSmallBiasRowWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row work upper bound

**Claim.** For all natural numbers $n$ and $\ell$, the work assigned to $n$ small-bias rows at degree $\ell$ is at most $n\bigl(\ell+n(W(\ell)+1)+2\ell+1\bigr)$, where $W(\ell)$ is the binary modular multiplication work.

**Proof.** Proceed by induction on $n$. At $n=0$, both the assigned work and the proposed bound are zero. For the step from $n$ to $n+1$, the recursive definition adds the work for power exponent $n+1$, the traversal work over a list of length $\ell$, and one additional unit. By the power work formula (\texttt{FABL.executableSmallBiasPowerWork_eq}), the first contribution is $\ell+(n+1)(W(\ell)+1)$; by the traversal work formula (\texttt{FABL.binaryConstructorTraversalWork_eq}), the second is $2\ell$. Adding these to the induction bound and using $W(\ell)\ge 0$ gives the stated bound with $n+1$ in place of $n$.

**Key facts.** `FABL.executableSmallBiasPowerWork_eq`, `FABL.binaryConstructorTraversalWork_eq`.
