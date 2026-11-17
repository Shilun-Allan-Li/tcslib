<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.executableVandermondePowerRowsWork_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power-Row Work Sum Formula

**Claim.** The work for $p$ power rows equals the sum, over $q=0,\ldots,p-1$, of the work for exponent $q+1$ together with the additional row cost $\ell+1$.

**Proof.** Induct on $p$. At $p=0$, both the recursively defined work and the empty sum are zero. For the successor case, the recursion adds the cost for exponent $p+1$ and the extra $\ell+1$ to the work for $p$ rows. By the induction hypothesis, that previous work is the sum through $q=p-1$; the finite-sum successor formula appends precisely the new term with $q=p$.
