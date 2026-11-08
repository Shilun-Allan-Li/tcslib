<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.executableVandermondePowerRowsWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power-Row Work Upper Bound

**Claim.** The work for $p$ power rows is at most $p\bigl(2\ell+p(M(\ell)+1)+1\bigr)$, where $M(\ell)$ is the work of one binary modular multiplication.

**Proof.** Induct on $p$. The zero-row case has zero work. For the successor step, the one-power cost is $\ell+(p+1)(M(\ell)+1)$ (`executableSmallBiasPowerWork_eq`), and the recursion adds this cost and $\ell+1$ to the work for $p$ rows. Substituting the induction bound and collecting terms gives the asserted bound with $p+1$ in place of $p$; the comparison uses only that $M(\ell)$ is nonnegative.

**Key facts.** `FABL.executableSmallBiasPowerWork_eq`.
